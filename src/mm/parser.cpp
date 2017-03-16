#include "mm/sys.hpp"
#include "peglib.h"

namespace mdl { namespace mm { namespace {

struct Parser {
private:
	struct Scope {
		set<Symbol> vars;
		set<Symbol> consts;
	};
	typedef vector<Scope> Stack;
	struct Context {
		Stack  stack;
		bool   source;
		Block* block;
		set<Block*> src_blocks;
	};
	peg::parser parser;

public:
	static const char* mm_syntax() {
		return R"(
			# Metamath grammar
		
            SOURCE  <- BLOCK
			BLOCK   <- ELEMENT*
			ELEMENT <- COMMENT / DISJ / ESS / TH / '${' BLOCK '$}'/ AX / CONST / VAR / FLO / INCLUDE 
			EXPR    <- (SYMB / COMMENT)+
			CONST   <-      '$c' EXPR '$.'
			VAR     <-      '$v' EXPR '$.'
			DISJ    <-      '$d' EXPR '$.'
			FLO     <- LAB  '$f' EXPR '$.'
			ESS     <- LAB  '$e' EXPR '$.'
			AX      <- LAB  '$a' EXPR '$.'
			TH      <- LAB  '$p' EXPR '$=' PROOF
			PROOF   <- REF+ '$.'
			REF     <- LAB
		
			SYMB    <- < (![ \t\r\n$] .)+ >
			LAB     <- < (![ \t\r\n$] .)+ >
			COMMENT <- '$(' < (!'$)' .)* > '$)'
            INCLUDE <- '$[' < (!'$]' .)* > '$]'
		
			%whitespace <- [ \t\r\n]*
		)";
	}
	Parser(uint label) : parser(mm_syntax()) {

		parser["SYMB"] = [](const peg::SemanticValues& sv) {
			return Symbol(Lex::toInt(sv.token()));
		};
		parser["LAB"] = [](const peg::SemanticValues& sv) {
			return Lex::toInt(sv.token());
		};
		parser["EXPR"] = [](const peg::SemanticValues& sv) {
			Vect expr;
			expr.reserve(sv.size());
			for (auto& s : sv) {
				if (s.is<Symbol>()) expr += s.get<Symbol>();
				else delete s.get<Comment*>();
			}
			return expr;
		};
		parser["CONST"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Constants* consts = new Constants { sv[0].get<Vect>() };
			for (Symbol c : consts->expr)
				context.get<std::shared_ptr<Context>>()->stack.back().consts.insert(c);
			return consts;
		};
		parser["VAR"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Variables* vars = new Variables { sv[0].get<Vect>() };
			for (Symbol c : vars->expr)
				context.get<std::shared_ptr<Context>>()->stack.back().vars.insert(c);
			return vars;
		};
		parser["DISJ"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Disjointed* disj = new Disjointed { sv[0].get<Vect>() };
			for (Symbol v : disj->expr)
				context.get<std::shared_ptr<Context>>()->stack.back().vars.insert(v);
			return disj;
		};
		parser["ESS"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Essential* ess = new Essential(sv[0].get<uint>(), sv[1].get<Vect>());
			markVars(ess->expr, context.get<std::shared_ptr<Context>>()->stack);
			return ess;
		};
		parser["FLO"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Floating* flo = new Floating(sv[0].get<uint>(), sv[1].get<Vect>());
			markVars(flo->expr, context.get<std::shared_ptr<Context>>()->stack);
			return flo;
		};
		parser["AX"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Axiom* ax = new Axiom(sv[0].get<uint>(), sv[1].get<Vect>());
			markVars(ax->expr, context.get<std::shared_ptr<Context>>()->stack);
			return ax;
		};
		parser["TH"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Theorem* th = new Theorem(sv[0].get<uint>(), sv[1].get<Vect>(), sv[2].get<Proof*>());
			markVars(th->expr, context.get<std::shared_ptr<Context>>()->stack);
			return th;
		};
		parser["PROOF"] = [](const peg::SemanticValues& sv) {
			return new Proof(std::move(sv.transform<Ref*>()));
		};
		parser["REF"] = [](const peg::SemanticValues& sv) {
			return new Ref(sv[0].get<uint>());
		};
		parser["COMMENT"] = [](const peg::SemanticValues& sv) {
			string text = sv.token();
			return new Comment(text.front() == ' ' ? text : " " + text);
		};
		parser["ELEMENT"] = [](const peg::SemanticValues& sv, peg::any& context) {
			// COMMENT / DISJ / ESS / TH / '${' BLOCK '$}'/ AX / CONST / VAR / FLO / INCLUDE
			Node node;
			switch (sv.choice()) {
			case 0: node = Node(sv[0].get<Comment*>());   break;
			case 1: node = Node(sv[0].get<Disjointed*>());break;
			case 2: node = Node(sv[0].get<Essential*>()); break;
			case 3: node = Node(sv[0].get<Theorem*>());   break;
			case 4: node = Node(sv[0].get<Block*>());     break;
			case 5: node = Node(sv[0].get<Axiom*>());     break;
			case 6: node = Node(sv[0].get<Constants*>()); break;
			case 7: node = Node(sv[0].get<Variables*>()); break;
			case 8: node = Node(sv[0].get<Floating*>());  break;
			case 9: node = Node(sv[0].get<Inclusion*>()); break;
			}
			context.get<std::shared_ptr<Context>>()->block->contents.push_back(node);
			return node;
		};
		parser["BLOCK"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Block* b = context.get<std::shared_ptr<Context>>()->block;
			b->contents = sv.transform<Node>();
			init_indexes(b->contents);
			return b;
		};
		parser["BLOCK"].enter = [](peg::any& c) {
			Context* context = c.get<std::shared_ptr<Context>>().get();
			context->block = new Block(context->block);
			if (!context->source) {
				context->stack.push_back(Scope());
			} else {
				context->src_blocks.insert(context->block);
			}
			context->source = false;
		};
		parser["BLOCK"].leave = [](peg::any& c) {
			Context* context = c.get<std::shared_ptr<Context>>().get();
			if (!context->src_blocks.count(context->block)) {
				context->stack.pop_back();
			} else {
				context->src_blocks.erase(context->block);
			}
			context->block = context->block->parent;
		};
		parser["SOURCE"] = [label](const peg::SemanticValues& sv, peg::any& context) {
			Source* src = new Source(label);
			src->block = sv[0].get<Block*>();
			return src;
		};
		parser["SOURCE"].enter = [](peg::any& context) {
			context.get<std::shared_ptr<Context>>()->source = true;
		};
		parser["INCLUDE"] = [](const peg::SemanticValues& sv, peg::any& context) {
			string name = sv.token();
			static map<string, mm::Inclusion*> included;
			if (included.count(name)) {
				mm::Inclusion* inc = included[name];
				return new mm::Inclusion(inc->source);
			} else {
				Path path = Sys::conf().in;
				path.name_ext(name);
				mm::Inclusion* inc = new mm::Inclusion();
				included[name] = inc;
				Source* src = parse(Lex::toInt(path.name), context.get<std::shared_ptr<Context>>());
				Sys::mod().math.sources.use(src->label, inc->source);
				return inc;
			}
		};
	}

	static Source* parse(uint label) {
		auto context = std::make_shared<Context>();
		context->stack.push_back(Scope());
		Source* src = parse(label, context);
		assert(!context->stack.empty());
		context->stack.pop_back();
		assert(context->stack.empty());
		return src;
	}

private:
	static Source* parse(uint label, std::shared_ptr<Context>& context) {
		Path path = Sys::conf().in;
		path.name = Lex::toStr(label);
		string data;
		path.read(data);
		Parser p(label);
		mdl::mm::Source* src = nullptr;
		peg::any c(context);
		if (!p.parser.parse<mdl::mm::Source*>(data.c_str(), c, src))
			throw Error("parsing failed", path.path());
		std::swap(data, src->data);
		return src;
	}
	static void markVars(Vect& expr, const Stack& stack) {
    	for (Symbol& s : expr) {
    		bool is_var   = false;
    		bool is_const = false;
			for (const Scope& vc : stack) {
				if (vc.vars.count(s)) is_var = true;
				if (vc.consts.count(s)) is_const = true;
			}
			if (is_var && is_const)
				throw Error("constant symbol is marked as variable", show_sy(s));
			if (!is_var && !is_const)
				throw Error("symbol is neither constant nor variable", show_sy(s));
			s.var = is_var;
		}
    }
	static void init_indexes(vector<Node>& nodes) {
		for (uint i = 0; i < nodes.size(); ++ i) nodes[i].ind = i;
	}
};

Source* parse(uint label) {
	return Parser::parse(label);
}

}

void parse() {
	Sys::timer()["read"].start();
	if (!parse(Lex::toInt(Sys::conf().in.name)))
		throw Error("parsing of " + Sys::conf().in.name + " failed");
	//cout << endl << *source;
	Sys::timer()["read"].stop();
}

}} // mdl::mm

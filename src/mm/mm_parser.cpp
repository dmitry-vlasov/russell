#include <mm_ast.hpp>
#include "peglib.h"

namespace mdl { namespace mm { namespace {

#define PARALLEL_PARSE

struct Parser {
private:
	struct Context {
		Context() : src_enter(false), block(nullptr) { }
		bool    src_enter;
		Block*  block;
		stack<Source*> source_stack;
		set<Block*>    src_blocks;

		Token token(const peg::SemanticValues& sv) const {
			return Token(source_stack.top(), sv.c_str(), sv.c_str() + sv.length());
		}
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
			CONST   <-      '$c' SYMB '$.'
			VAR     <-      '$v' SYMB '$.'
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
			return Lex::toInt(sv.token());
		};
		parser["LAB"] = [](const peg::SemanticValues& sv) {
			return Lex::toInt(sv.token());
		};
		parser["EXPR"] = [](const peg::SemanticValues& sv) {
			Expr expr;
			expr.reserve(sv.size());
			for (auto& s : sv) {
				if (s.is<uint>()) expr.emplace_back(s.get<uint>());
				else delete s.get<Comment*>();
			}
			return expr;
		};
		parser["CONST"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			uint s = sv[0].get<uint>();
			return new Constant(s, c.token(sv));
		};
		parser["VAR"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			uint v = sv[0].get<uint>();
			return new Variable(v, c.token(sv));
		};
		parser["DISJ"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			return new Disjointed(sv[0].get_val<Expr>(), c.token(sv));
		};
		parser["ESS"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			return new Essential(sv[0].get<uint>(), sv[1].get_val<Expr>(), c.token(sv));
		};
		parser["FLO"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			return new Floating(sv[0].get<uint>(), sv[1].get_val<Expr>(), c.token(sv));
		};
		parser["AX"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			return new Axiom(sv[0].get<uint>(), sv[1].get_val<Expr>(), c.token(sv));
		};
		parser["TH"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			return new Theorem(sv[0].get<uint>(), sv[1].get_val<Expr>(), sv[2].get<Proof*>(), c.token(sv));
		};
		parser["PROOF"] = [](const peg::SemanticValues& sv) {
			return new Proof(std::move(sv.transform<Ref*>()));
		};
		parser["REF"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			return new Ref(sv[0].get<uint>(), c.token(sv));
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
			case 6: node = Node(sv[0].get<Constant*>()); break;
			case 7: node = Node(sv[0].get<Variable*>()); break;
			case 8: node = Node(sv[0].get<Floating*>());  break;
			case 9: node = Node(sv[0].get<Inclusion*>()); break;
			}
			context.get<Context*>()->block->contents.push_back(node);
			return node;
		};
		parser["BLOCK"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Block* b = c.block;
			b->contents = sv.transform<Node>();
			b->token = c.token(sv);
			init_indexes(b->contents);
			return b;
		};
		parser["BLOCK"].enter = [](peg::any& c) {
			Context* context = c.get<Context*>();
			context->block = new Block(context->block);
			if (context->src_enter) {
				context->src_blocks.insert(context->block);
			}
			context->src_enter = false;
		};
		parser["BLOCK"].leave = [](peg::any& c) {
			Context* context = c.get<Context*>();
			if (context->src_blocks.count(context->block)) {
				context->src_blocks.erase(context->block);
			}
			context->block = context->block->parent;
		};
		parser["SOURCE"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			c.source_stack.top()->block = sv[0].get<Block*>();
			Source* s = c.source_stack.top();
			c.source_stack.pop();
			return s;
		};
		parser["SOURCE"].enter = [](peg::any& context) {
			Context& c = *context.get<Context*>();
			c.src_enter = true;
		};
		parser["INCLUDE"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			uint id = Sys::make_name(sv.token());
			Source* s = Sys::mod().math.get<Source>().access(id);
			const bool primary = !s->parsed;
#ifndef PARALLEL_PARSE
			if (primary) parse(id);
#endif
			return new Inclusion(id, primary, c.token(sv));
		};
		parser.log = [label](size_t ln, size_t col, const std::string& err_msg) {
			std::stringstream ss;
			ss << "file: " << Lex::toStr(label) << ", line: " << ln << ", col: " << col << ": " << err_msg << std::endl;
			throw Error(ss.str());
		};
	}

	static void parse(uint label) {
		Context* context = new Context();
		try {
			Source* src = Sys::mod().math.get<Source>().access(label);
			context->source_stack.push(src);
			Parser p(label);
			peg::any c(context);
			if (!p.parser.parse<mdl::mm::Source*>(src->data().c_str(), c, src)) {
				throw Error("parsing of " + Lex::toStr(label) + " failed");
			}
			src->parsed = true;
		} catch(Error& e) {
			delete context;
			throw e;
		}
		delete context;
	}

private:
	static void init_indexes(vector<Node>& nodes) {
		for (uint i = 0; i < nodes.size(); ++ i) nodes[i].ind = i;
	}
};

}

void parse(uint label) {
#ifdef PARALLEL_PARSE
	vector<uint> labels;
	for (auto p : Sys::mod().math.get<Source>())
		if (!p.second.data->parsed) labels.push_back(p.first);
	tbb::parallel_for (tbb::blocked_range<size_t>(0, labels.size()),
		[labels] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i)
				Parser::parse(labels[i]);
		}
	);
#else
	for (auto p : Sys::mod().math.get<Source>())
		if (!p.second.data->parsed) Parser::parse(p.first);
#endif
}

}} // mdl::mm

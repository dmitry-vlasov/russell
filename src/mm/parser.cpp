#include <mm_ast.hpp>
#include "peglib.h"

namespace mdl { namespace mm { namespace {

struct Parser {
private:
	struct Scope {
		set<Symbol> vars;
		set<Symbol> consts;
	};
	struct Context {
		Context() : src_enter(false), block(nullptr) { }
		bool    src_enter;
		Block*  block;
		vector<Scope>  scope_stack;
		stack<Source*> source_stack;
		set<Block*>    src_blocks;

		Token token(const peg::SemanticValues& sv) const {
			return Token(source_stack.top(), sv.c_str(), sv.c_str() + sv.length());
		}
	};
	peg::parser parser;

	static vector<Patch> const_patches;

public:
	static const char* mm_syntax() {
		return R"(
			# Metamath grammar
		
            SOURCE  <- BLOCK
			BLOCK   <- ELEMENT*
			ELEMENT <- COMMENT / DISJ / ESS / TH / '${' BLOCK '$}'/ AX / CONST / VAR / FLO / INCLUDE 
			EXPR    <- (SYMB / COMMENT)+
			CONST   <-      '$c' SYMB '$.'
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
			Context& c = *context.get<Context*>();
			Symbol s = sv[0].get<Symbol>();
			Constant* constant = new Constant(s, c.token(sv));
			c.scope_stack.back().consts.insert(s);
			return constant;
		};
		parser["VAR"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Variables* vars = new Variables(sv[0].get<Vect>(), c.token(sv));
			for (Symbol v : vars->expr)
				c.scope_stack.back().vars.insert(v);
			return vars;
		};
		parser["DISJ"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Disjointed* disj = new Disjointed(sv[0].get<Vect>(), c.token(sv));
			for (Symbol v : disj->expr)
				c.scope_stack.back().vars.insert(v);
			return disj;
		};
		parser["ESS"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Essential* ess = new Essential(sv[0].get<uint>(), sv[1].get<Vect>(), c.token(sv));
			ess->token = c.token(sv);
			markVars(ess->expr, c.scope_stack);
			return ess;
		};
		parser["FLO"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Floating* flo = new Floating(sv[0].get<uint>(), sv[1].get<Vect>(), c.token(sv));
			flo->token = c.token(sv);
			markVars(flo->expr, c.scope_stack);
			return flo;
		};
		parser["AX"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Axiom* ax = new Axiom(sv[0].get<uint>(), sv[1].get<Vect>(), c.token(sv));
			ax->token = c.token(sv);
			markVars(ax->expr, c.scope_stack);
			return ax;
		};
		parser["TH"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			Theorem* th = new Theorem(sv[0].get<uint>(), sv[1].get<Vect>(), sv[2].get<Proof*>(), c.token(sv));
			markVars(th->expr, c.scope_stack);
			th->token = c.token(sv);
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
			case 6: node = Node(sv[0].get<Constant*>()); break;
			case 7: node = Node(sv[0].get<Variables*>()); break;
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
			if (!context->src_enter) {
				context->scope_stack.push_back(Scope());
			} else {
				context->src_blocks.insert(context->block);
			}
			context->src_enter = false;
		};
		parser["BLOCK"].leave = [](peg::any& c) {
			Context* context = c.get<Context*>();
			if (!context->src_blocks.count(context->block)) {
				context->scope_stack.pop_back();
			} else {
				context->src_blocks.erase(context->block);
			}
			context->block = context->block->parent;
		};
		parser["SOURCE"] = [label](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			c.source_stack.top()->block = sv[0].get<Block*>();
			Source* s = c.source_stack.top();
			c.source_stack.pop();
			return s;
		};
		parser["SOURCE"].enter = [label](peg::any& context) {
			Context& c = *context.get<Context*>();
			c.src_enter = true;
			c.source_stack.push(new Source(label));
		};
		parser["INCLUDE"] = [](const peg::SemanticValues& sv, peg::any& context) {
			Context& c = *context.get<Context*>();
			uint id = Sys::make_name(sv.token());
			const bool primary = !Sys::get().math.get<Source>().has(id);
			Source* src = primary ? parse(id, &c) : Sys::mod().math.get<Source>().access(id);
			c.source_stack.top()->include(src);
			return new Inclusion(id, primary);
		};
		parser.log = [label](size_t ln, size_t col, const std::string& err_msg) {
			std::stringstream ss;
			ss << "file: " << Lex::toStr(label) << ", line: " << ln << ", col: " << col << ": " << err_msg << std::endl;
			throw Error(ss.str());
		};
	}

	static Source* parse(uint label) {
		Context* context = new Context();
		context->scope_stack.push_back(Scope());
		Source* src = parse(label, context);
		assert(!context->scope_stack.empty());
		context->scope_stack.pop_back();
		assert(context->scope_stack.empty());
		delete context;
		return src;
	}

private:
	static Source* parse(uint label, Context* context) {
		Path path(Lex::toStr(label), Sys::conf().get("root"), "mm");
		string data;
		path.read(data, &const_patches);
		Parser p(label);
		mdl::mm::Source* src = nullptr;
		peg::any c(context);
		if (!p.parser.parse<mdl::mm::Source*>(data.c_str(), c, src))
			throw Error("parsing failed", path.path());
		std::swap(data, src->data);
		return src;
	}
	static void markVars(Vect& expr, const vector<Scope>& stack) {
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

vector<Patch> Parser::const_patches = {
{
R"(
  $c har ~<_* $.
)",
R"(
  $c har $.
  $c ~<_* $.
)"
},
{
R"(
  $c Fin1a Fin2 Fin3 Fin4 Fin5 Fin6 Fin7 $.
)",
R"(
  $c Fin1a $.
  $c Fin2 $.
  $c Fin3 $.
  $c Fin4 $.
  $c Fin5 $.
  $c Fin6 $.
  $c Fin7 $.
)"
},
{
R"(
  $c numer denom $.
)",
R"(
  $c numer $.
  $c denom $.
)"
},
{
R"(
  $c Xs_ ^s $.
)",
R"(
  $c Xs_ $.
  $c ^s $.
)"
},
{
R"(
  $c Moore mrCls ACS $.
)",
R"(
  $c Moore $.
  $c mrCls $.
  $c ACS $.
)"
},
{
R"(
  $c Preset Dirset $.
)",
R"(
  $c Preset $.
  $c Dirset $.
)"
},
{
R"(
  $c <" "> $.
)",
R"(
  $c <" $.
  $c "> $.
)"
},
{
R"(
  $c No <s bday $.
)",
R"(
  $c No $.
  $c <s $.
  $c bday $.
)"
},
{
R"(
  $c (x) Bigcup SSet Trans Limits Fix Funs Singleton Singletons Image Cart $.
  $c Img Domain Range pprod Apply Cup Cap Succ Funpart FullFun Restrict $.
)",
R"(
  $c (x) $.
  $c Bigcup $.
  $c SSet $.
  $c Trans $.
  $c Limits $.
  $c Fix $.
  $c Funs $.
  $c Singleton $.
  $c Singletons $.
  $c Image $.
  $c Cart $.

  $c Img $.
  $c Domain $.
  $c Range $.
  $c pprod $.
  $c Apply $.
  $c Cup $.
  $c Cap $.
  $c Succ $.
  $c Funpart $.
  $c FullFun $.
  $c Restrict $.
)"
},
{
R"(
  $c << >> XX. $.
)",
R"(
  $c << $.
  $c >> $.
  $c XX. $.
)"
},
{
R"(
  $c EE Btwn Cgr $.
)",
R"(
  $c EE $.
  $c Btwn $.
  $c Cgr $.
)"
},
{
R"(
  $c InnerFiveSeg Cgr3 Colinear FiveSeg $.
)",
R"(
  $c InnerFiveSeg $.
  $c Cgr3 $.
  $c Colinear $.
  $c FiveSeg $.
)"
},
{
R"(
  $c Line LinesEE Ray $.
)",
R"(
  $c Line $.
  $c LinesEE $.
  $c Ray $.
)"
},
{
R"(
  $c Pell1QR Pell14QR Pell1234QR PellFund []NN $.
)",
R"(
  $c Pell1QR $.
  $c Pell14QR $.
  $c Pell1234QR $.
  $c PellFund $.
  $c []NN $.
)"
},
{
R"(
  $c rmX rmY $.
)",
R"(
  $c rmX $.
  $c rmY $.
)"
},
{
R"(
  $c freeLMod unitVec $.
)",
R"(
  $c freeLMod $.
  $c unitVec $.
)"
},
{
R"(
  $c LIndF LIndS $.
)",
R"(
  $c LIndF $.
  $c LIndS $.
)"
},
{
R"(
  $c Monic Poly< $.
)",
R"(
  $c Monic $.
  $c Poly< $.
)"
},
{
R"(
  $c degAA minPolyAA $.
)",
R"(
  $c degAA $.
  $c minPolyAA $.
)"
},
{
R"(
  $c _ZZ IntgOver $.
)",
R"(
  $c _ZZ $.
  $c IntgOver $.
)"
},
{
R"(
  $c maMul Mat $.
)",
R"(
  $c maMul $.
  $c Mat $.
)"
},
{
R"(
  $c maDet maAdju $.
)",
R"(
  $c maDet $.
  $c maAdju $.
)"
},
{
R"(
  $c TopSep TopLnd $.
)",
R"(
  $c TopSep $.
  $c TopLnd $.
)"
},
{
R"(
  $c +r -r .v PtDf RR3 plane3 line3 $.
)",
R"(
  $c +r $.
  $c -r $.
  $c .v $.
  $c PtDf $.
  $c RR3 $.
  $c plane3 $.
  $c line3 $.
)"
},
{
R"(
  $c LPIdeal LPIR $.
)",
R"(
  $c LPIdeal $.
  $c LPIR $.
)"
}
};

}

void parse(uint label) {
	delete Sys::get().math.get<Source>().access(label);
	if (!Parser::parse(label))
		throw Error("parsing of " + Lex::toStr(label) + " failed");
	//cout << endl << *src_enter;
}

}} // mdl::mm

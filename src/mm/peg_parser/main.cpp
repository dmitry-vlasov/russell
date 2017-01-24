#include <iostream>

#include "peglib.h"
#include "mm/globals.hpp"
#include "mm_src.hpp"

using namespace std;
using namespace peg;

namespace mdl { namespace mm {

void init_indexes(vector<Node>& nodes) {
	for (uint i = 0; i < nodes.size(); ++ i) nodes[i].ind = i;
}

struct Scope {
		Scope(Block* b = nullptr) : vars(), consts(), block(b) { }
		set<Symbol> vars;
		set<Symbol> consts;
		Block*      block;
	};
	typedef vector<Scope> Stack;

void markVars(Expr& expr, const Stack& stack) {
    	for (Symbol& s : expr.symbols) {
    		bool is_var   = false;
    		bool is_const = false;
			for (const Scope& vc : stack) {
				if (vc.vars.find(s) != vc.vars.end()) is_var = true;
				if (vc.consts.find(s) != vc.consts.end()) is_const = true;
			}
			if (is_var && is_const)
				throw Error("constant symbol is marked as variable", show_sy(s));
			if (!is_var && !is_const)
				throw Error("symbol is neither constant nor variable", show_sy(s));
			s.var = is_var;
		}
    }
struct Parser {


	peg::parser parser;


	static const char* mm_syntax() {
		return R"(
			# Metamath grammar
		
			SOURCE  <- ELEMENT*
			ELEMENT <- COMMENT / CONST / VAR / DISJ / FLO / ESS / AX / TH /  BLOCK
			CONST   <-      '$c' SYMB+ '$.'
			VAR     <-      '$v' SYMB+ '$.'
			DISJ    <-      '$d' SYMB+ '$.'
			FLO     <- LAB  '$f' SYMB+ '$.'
			ESS     <- LAB  '$e' SYMB+ '$.'
			AX      <- LAB  '$a' SYMB+ '$.'
			TH      <- LAB  '$p' SYMB+ '$=' PROOF
			PROOF   <- REF+ '$.'
			REF     <- LAB
			BLOCK   <- '${' ELEMENT* '$}' 
		
			SYMB    <- < (![ \t\r\n$] .)+ >
			LAB     <- < [a-zA-Z0-9-_.]+ >
			COMMENT <- '$(' < (!'$)' .)* > '$)'
		
			%whitespace <- [ \t\r\n]*
		)";
	}
	Parser() : parser(mm_syntax()) {

		parser["SYMB"] = [](const SemanticValues& sv) {
			return Symbol(Mm::mod().lex.symbols.toInt(sv.token()));
		};
		parser["LAB"] = [](const SemanticValues& sv) {
			return Mm::mod().lex.labels.toInt(sv.token());
		};
		parser["CONST"] = [](const SemanticValues& sv, any& stack) {
			Constants* consts = new Constants { Expr(sv.transform<Symbol>()) };
			for (Symbol c : consts->expr.symbols)
				stack.get<Stack&>().back().consts.insert(c);
			return consts;
		};
		parser["VAR"] = [](const SemanticValues& sv, any& stack) {
			Variables* vars = new Variables { Expr(sv.transform<Symbol>()) };
			for (Symbol c : vars->expr.symbols)
				stack.get<Stack&>().back().vars.insert(c);
			return vars;
		};
		parser["DISJ"] = [](const SemanticValues& sv, any& stack) {
			return new Disjointed { Expr(sv.transform<Symbol>()) };
		};
		parser["ESS"] = [](const SemanticValues& sv, any& stack) {
			Essential* ess = new Essential { sv[0].get<uint>(), Expr(sv.transform<Symbol>(1)) };
			markVars(ess->expr, stack.get<Stack&>());
			Mm::mod().math.essentials[ess->label] = ess;
			return ess;
		};
		parser["FLO"] = [](const SemanticValues& sv, any& stack) {
			Floating* flo = new Floating { sv[0].get<uint>(), Expr(sv.transform<Symbol>(1)) };
			markVars(flo->expr, stack.get<Stack&>());
			Mm::mod().math.floatings[flo->label] = flo;
			return flo;
		};
		parser["AX"] = [](const SemanticValues& sv, any& stack) {
			Axiom* ax = new Axiom { sv[0].get<uint>(), Expr(sv.transform<Symbol>(1)), (uint) -1 };
			markVars(ax->expr, stack.get<Stack&>());
			Mm::mod().math.axioms[ax->label] = ax;
			return ax;
		};
		parser["TH"] = [](const SemanticValues& sv, any& stack) {
			uint sz = sv.size();
			Theorem* th = new Theorem();
			th->label = sv[0].get<uint>();
			th->expr = Expr(sv.transform<Symbol>(1, sz - 1));
			th->proof = sv[sz - 1].get<Proof*>();
			markVars(th->expr, stack.get<Stack&>());
			Mm::mod().math.theorems[th->label] = th;
			return th;
		};
		parser["PROOF"] = [](const SemanticValues& sv) {
			Proof* pr = new Proof();
			pr->refs = sv.transform<Ref>();
			return pr;
		};
		parser["REF"] = [](const SemanticValues& sv) {
			uint lab = sv[0].get<uint>();
			Mm::Math& math = Mm::mod().math;
			if (math.floatings.count(lab))
				return Ref(math.floatings[lab]);
			else if (math.essentials.count(lab))
				return Ref(math.essentials[lab]);
			else if (math.axioms.count(lab))
				return Ref(math.axioms[lab]);
			else if (math.theorems.count(lab))
				return Ref(math.theorems[lab]);
			else
				throw Error("unknown label in proof", Mm::get().lex.labels.toStr(lab));
		};
		parser["COMMENT"] = [](const SemanticValues& sv) {
			return new Comment(sv.token());
		};
		parser["ELEMENT"] = [](const SemanticValues& sv, any& stack) {
			// COMMENT / CONST / VAR / DISJ / FLO / ESS / AX / TH /  BLOCK
			switch (sv.choice()) {
			case 0: return Node(sv[0].get<Comment*>());
			case 1: return Node(sv[0].get<Constants*>());
			case 2: return Node(sv[0].get<Variables*>());
			case 3: return Node(sv[0].get<Disjointed*>());
			case 4: return Node(sv[0].get<Floating*>());
			case 5: return Node(sv[0].get<Essential*>());
			case 6: return Node(sv[0].get<Axiom*>());
			case 7: return Node(sv[0].get<Theorem*>());
			case 8: return Node(sv[0].get<Block*>());
			}
			return Node();
		};
		parser["BLOCK"] = [](const SemanticValues& sv, any& stack) {
			Block* b = stack.get<Stack&>().back().block;
			b->contents = sv.transform<Node>();
			init_indexes(b->contents);
			return b;
		};
		parser["BLOCK"].enter = [](any& s) {
			Stack& stack = s.get<Stack&>();
			stack.push_back(Scope(new Block(stack.back().block)));
		};
		parser["BLOCK"].leave = [](any& stack) {
			stack.get<Stack&>().pop_back();
		};
		parser["SOURCE"] = [](const SemanticValues& sv, any& s) {
			Source* src = new Source("aaa", "bbb");
			Stack& stack = s.get<Stack&>();
			stack.back().block->contents = sv.transform<Node>();
			src->block = stack.back().block;
			init_indexes(src->block->contents);
			return src;
		};
		parser["SOURCE"].enter = [](any& s) {
			Stack& stack = s.get<Stack&>();
			stack.push_back(Scope(new Block()));
		};
		parser["SOURCE"].leave = [](any& stack) {
			stack.get<Stack&>().pop_back();
		};
	}

	Source* parse(const char* src) {
		mdl::mm::Source* s = nullptr;
		Stack stack;
		any any_stack(stack);
		if (parser.parse<mdl::mm::Source*>(mm_src, any_stack, s)) {
			return s;
		} else {
			return nullptr;
		}
	}
private:

};

}}

int main() {
	mdl::mm::Parser p;
	mdl::mm::Source* s = nullptr;
	if (p.parser.parse<mdl::mm::Source*>(mm_src, s)) {
		cout << *s << endl;
		cout << "SUCCESS PARSE" << endl;
	} else {
		cout << "FAIL PARSE" << endl;
	}
	return 0;
}



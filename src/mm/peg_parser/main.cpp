#include <iostream>

#include "peglib.h"
#include "mm/globals.hpp"
#include "mm_src.hpp"

using namespace std;
using namespace peg;

namespace mdl { namespace mm {

struct Parser {
	struct Scope {
		Scope(Block* b = nullptr) : vars(), consts(), block(b) { }
		set<Symbol> vars;
		set<Symbol> consts;
		Block*      block;
	};
	typedef vector<Scope> Stack;

	peg::parser parser;


	static const char* mm_syntax() {
		return R"(
			# Metamath grammar
		
            SOURCE  <- BLOCK
			BLOCK   <- ELEMENT*
			ELEMENT <- COMMENT / CONST / VAR / DISJ / FLO / ESS / AX / TH / INCLUDE / '${' BLOCK '$}'
			CONST   <-      '$c' SYMB+ '$.'
			VAR     <-      '$v' SYMB+ '$.'
			DISJ    <-      '$d' SYMB+ '$.'
			FLO     <- LAB  '$f' SYMB+ '$.'
			ESS     <- LAB  '$e' SYMB+ '$.'
			AX      <- LAB  '$a' SYMB+ '$.'
			TH      <- LAB  '$p' SYMB+ '$=' PROOF
			PROOF   <- REF+ '$.'
			REF     <- LAB
		
			SYMB    <- < (![ \t\r\n$] .)+ >
			LAB     <- < [a-zA-Z0-9-_.]+ >
			COMMENT <- '$(' < (!'$)' .)* > '$)'
            INCLUDE <- '$[' < (!'$]' .)* > '$]'
		
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
				stack.get<shared_ptr<Stack>>()->back().consts.insert(c);
			return consts;
		};
		parser["VAR"] = [](const SemanticValues& sv, any& stack) {
			Variables* vars = new Variables { Expr(sv.transform<Symbol>()) };
			for (Symbol c : vars->expr.symbols)
				stack.get<shared_ptr<Stack>>()->back().vars.insert(c);
			return vars;
		};
		parser["DISJ"] = [](const SemanticValues& sv, any& stack) {
			return new Disjointed { Expr(sv.transform<Symbol>()) };
		};
		parser["ESS"] = [](const SemanticValues& sv, any& stack) {
			Essential* ess = new Essential { sv[0].get<uint>(), Expr(sv.transform<Symbol>(1)) };
			markVars(ess->expr, stack.get<shared_ptr<Stack>>().get());
			Mm::mod().math.essentials[ess->label] = ess;
			return ess;
		};
		parser["FLO"] = [](const SemanticValues& sv, any& stack) {
			Floating* flo = new Floating { sv[0].get<uint>(), Expr(sv.transform<Symbol>(1)) };
			markVars(flo->expr, stack.get<shared_ptr<Stack>>().get());
			Mm::mod().math.floatings[flo->label] = flo;
			return flo;
		};
		parser["AX"] = [](const SemanticValues& sv, any& stack) {
			Axiom* ax = new Axiom { sv[0].get<uint>(), Expr(sv.transform<Symbol>(1)), (uint) -1 };
			markVars(ax->expr, stack.get<shared_ptr<Stack>>().get());
			Mm::mod().math.axioms[ax->label] = ax;
			return ax;
		};
		parser["TH"] = [](const SemanticValues& sv, any& stack) {
			uint sz = sv.size();
			Theorem* th = new Theorem();
			th->label = sv[0].get<uint>();
			th->expr = Expr(sv.transform<Symbol>(1, sz - 1));
			th->proof = sv[sz - 1].get<Proof*>();
			markVars(th->expr, stack.get<shared_ptr<Stack>>().get());
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
		parser["ELEMENT"] = [](const SemanticValues& sv, any& s) {
			// COMMENT / CONST / VAR / DISJ / FLO / ESS / AX / TH /  BLOCK
			Node node;
			switch (sv.choice()) {
			case 0: node = Node(sv[0].get<Comment*>());   break;
			case 1: node = Node(sv[0].get<Constants*>()); break;
			case 2: node = Node(sv[0].get<Variables*>()); break;
			case 3: node = Node(sv[0].get<Disjointed*>());break;
			case 4: node = Node(sv[0].get<Floating*>());  break;
			case 5: node = Node(sv[0].get<Essential*>()); break;
			case 6: node = Node(sv[0].get<Axiom*>());     break;
			case 7: node = Node(sv[0].get<Theorem*>());   break;
			case 8: node = Node(sv[0].get<Inclusion*>());     break;
			case 9: node = Node(sv[0].get<Block*>());     break;
			}
			auto stack = s.get<shared_ptr<Stack>>();
			stack->back().block->contents.push_back(node);
			return node;
		};
		parser["BLOCK"] = [](const SemanticValues& sv, any& s) {
			auto stack = s.get<shared_ptr<Stack>>();
			Block* b = stack->back().block;
			b->contents = sv.transform<Node>();
			init_indexes(b->contents);
			return b;
		};
		parser["BLOCK"].enter = [](any& s) {
			auto stack = s.get<shared_ptr<Stack>>();
			Block* parent = stack->size() ? stack->back().block : nullptr;
			Block* child = new Block(parent);
			stack->push_back(Scope(child));
		};
		parser["BLOCK"].leave = [](any& s) {
			auto stack = s.get<shared_ptr<Stack>>();
			stack->pop_back();
		};
		parser["SOURCE"] = [](const SemanticValues& sv, any& s) {
			Source* src = new Source("aaa", "bbb");
			src->block = sv[0].get<Block*>();
			return src;
		};
		parser["INCLUDE"] = [](const SemanticValues& sv) {
			mdl::include<Source, Parser, Inclusion>(
				sv.token(),
				Mm::get().config.root,
				" ",
				[] (Inclusion* inc) -> Source* { return inc->source; }
			);
		};
	}

	Source* parse(const char* src) {
		mdl::mm::Source* s = nullptr;
		auto stack = make_shared<Stack>();
		any any_stack(stack);
		if (parser.parse<mdl::mm::Source*>(src, any_stack, s)) {
			return s;
		} else {
			return nullptr;
		}
	}

	static bool parse(LocationIter& beg, LocationIter& end, auto space, mdl::mm::Source& src) {
		Parser p;
		auto stack = make_shared<Stack>();
		any any_stack(stack);
		return p.parser.parse<mdl::mm::Source&>(&*beg, any_stack, src);
	}

private:
	static void markVars(Expr& expr, const Stack* stack) {
    	for (Symbol& s : expr.symbols) {
    		bool is_var   = false;
    		bool is_const = false;
			for (const Scope& vc : *stack) {
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
	static void init_indexes(vector<Node>& nodes) {
		for (uint i = 0; i < nodes.size(); ++ i) nodes[i].ind = i;
	}
};

}}

int main() {
	mdl::mm::Parser p;
	if (mdl::mm::Source* s = p.parse(mm_src)) {
		cout << *s << endl;
		cout << "SUCCESS PARSE" << endl;
		delete s;
	} else {
		cout << "FAIL PARSE" << endl;
	}
	return 0;
}



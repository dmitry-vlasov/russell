#include <iostream>

#include "peglib.h"
#include "mm/globals.hpp"
#include "mm_src.hpp"

using namespace std;
using namespace peg;
using namespace mdl;
using namespace mm;

auto mm_syntax = R"(
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

void init_indexes(vector<Node>& nodes) {
	for (uint i = 0; i < nodes.size(); ++ i) nodes[i].ind = i;
}

int main() {


	peg::parser parser;
	if (parser.load_grammar(mm_syntax)) {
		cout << "SUCCESS GR" << endl;
	} else {
		cout << "FAIL GR" << endl;
	}
	parser.enable_ast();

	parser["SYMB"] = [](const SemanticValues& sv) {
		return Symbol(mm::Mm::mod().lex.symbols.toInt(sv.token()));
	};
	parser["LAB"] = [](const SemanticValues& sv) {
		return mm::Mm::mod().lex.labels.toInt(sv.token());
	};
	parser["CONST"] = [](const SemanticValues& sv) {
		return new mm::Constants { Expr(sv.transform<Symbol>()) };
	};
	parser["VAR"] = [](const SemanticValues& sv) {
		return new mm::Variables { Expr(sv.transform<Symbol>()) };
	};
	parser["DISJ"] = [](const SemanticValues& sv) {
		return new mm::Disjointed { Expr(sv.transform<Symbol>()) };
	};
	parser["ESS"] = [](const SemanticValues& sv) {
		mm::Essential* ess = new mm::Essential { sv[0].get<uint>(), Expr(sv.transform<Symbol>(1)) };
		Mm::mod().math.essentials[ess->label] = ess;
		return ess;
	};
	parser["FLO"] = [](const SemanticValues& sv) {
		mm::Floating* flo = new mm::Floating { sv[0].get<uint>(), Expr(sv.transform<Symbol>(1)) };
		Mm::mod().math.floatings[flo->label] = flo;
		return flo;
	};
	parser["AX"] = [](const SemanticValues& sv) {
		mm::Axiom* ax = new mm::Axiom { sv[0].get<uint>(), Expr(sv.transform<Symbol>(1)), (uint) -1 };
		Mm::mod().math.axioms[ax->label] = ax;
		return ax;
	};
	parser["TH"] = [](const SemanticValues& sv) {
		uint sz = sv.size();
		mm::Theorem* th = new mm::Theorem();
		th->label = sv[0].get<uint>();
		th->expr = Expr(sv.transform<Symbol>(1, sz - 1));
		th->proof = sv[sz - 1].get<mm::Proof*>();
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
		return new mm::Comment(sv.token());
	};
	parser["ELEMENT"] = [](const SemanticValues& sv) {
		// COMMENT / CONST / VAR / DISJ / FLO / ESS / AX / TH /  BLOCK
		switch (sv.choice()) {
		case 0: return mm::Node(sv[0].get<mm::Comment*>());
		case 1: return mm::Node(sv[0].get<mm::Constants*>());
		case 2: return mm::Node(sv[0].get<mm::Variables*>());
		case 3: return mm::Node(sv[0].get<mm::Disjointed*>());
		case 4: return mm::Node(sv[0].get<mm::Floating*>());
		case 5: return mm::Node(sv[0].get<mm::Essential*>());
		case 6: return mm::Node(sv[0].get<mm::Axiom*>());
		case 7: return mm::Node(sv[0].get<mm::Theorem*>());
		case 8: return mm::Node(sv[0].get<mm::Block*>());
		}
		return mm::Node();
	};
	parser["BLOCK"] = [](const SemanticValues& sv) {
		mm::Block* b =  new mm::Block();
		b->contents = sv.transform<mm::Node>();
		init_indexes(b->contents);
		return b;
	};
	parser["SOURCE"] = [](const SemanticValues& sv) {
		mm::Source* s =  new mm::Source("aaa", "bbb");
		s->block->contents = sv.transform<mm::Node>();
		init_indexes(s->block->contents);
		return s;
	};

	mm::Source* s = nullptr;
	if (parser.parse<mm::Source*>(mm_src, s)) {
		cout << *s << endl;
		cout << "SUCCESS PARSE" << endl;
	} else {
		cout << "FAIL PARSE" << endl;
	}
	return 0;
}

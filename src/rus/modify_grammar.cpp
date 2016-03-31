#include "rus/ast.hpp"
#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace {

void modify_grammar(Expr& ex) {
	Expr e = assemble(ex);
	ex.destroy();
	ex = e;
}

void transform(Expr& ex) {
	if (ex.first->symb.type && ex.first != ex.last) {
		Expr e = assemble(ex);
		e.push_front(Symbol("("));
		e.push_back(Symbol(")"));
		e.first->init = e.first->next->init;
		e.last->final = e.last->prev->final;
		e.first->next->init.clear();
		e.last->prev->final.clear();
		for (auto t : e.first->init) t->first = e.first;
		for (auto t : e.last->final) t->last = e.last;
		ex.destroy();
		ex = e;
	}
}

void modify_grammar(Rule* rule) {
	transform(rule->term);
}


void modify_grammar(Assertion& ass) {
	for (auto hyp  : ass.hyps)  modify_grammar(hyp->expr);
	for (auto prop : ass.props) modify_grammar(prop->expr);
}


void modify_grammar(Def* def) {
	modify_grammar(def->ass);
	modify_grammar(def->dfm);
	modify_grammar(def->dfs);
	if (def->prop.first->symb != Symbol("(")) {
		def->prop.push_front(Symbol("("));
		def->prop.push_back(Symbol(")"));
	}
}


void modify_grammar(Proof* proof) {
	for (auto el : proof->elems)
		if (el.kind == Proof::Elem::STEP) {
			modify_grammar(el.val.step->expr);
			if (el.val.step->kind == Step::CLAIM)
				modify_grammar(el.val.step->proof);
		}
}

void modify_grammar(Node& n) {
	switch (n.kind) {
	case Node::CONST:   break;
	case Node::TYPE :   break;
	case Node::RULE:    modify_grammar(n.val.rul);      break;
	case Node::AXIOM:   modify_grammar(n.val.ax->ass);  break;
	case Node::DEF:     modify_grammar(n.val.def);      break;
	case Node::THEOREM: modify_grammar(n.val.thm->ass); break;
	case Node::PROOF:   modify_grammar(n.val.prf);      break;
	case Node::THEORY:
		for (auto m : n.val.thy->nodes) modify_grammar(m); break;
	default : assert(false); break;
	}
}

}

void modify_grammar(Source* src) {
	for (auto n : src->theory->nodes)
		modify_grammar(n);
}


}} // mdl::rus


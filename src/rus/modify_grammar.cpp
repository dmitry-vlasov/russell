#include "rus/ast.hpp"
#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace {

/**
 * Struct which stores the id's of the
 * proper rule names
 */
struct Ids {
	const uint co;
	const uint cqs;
	const uint cdiv;
	static Ids& get() { static Ids ids; return ids; }
private:
	Ids() :
		co(Rus::get().lex.ids.getInt("co")),
		cqs(Rus::get().lex.ids.getInt("cqs")),
		cdiv(Rus::get().lex.ids.getInt("cdiv")) { }
};


/**
 * Struct which stores rules with
 * the proper names
 */
struct Rules {
	Rule* const cqs;
	static Rules& get() { static Rules rules; return rules; }
private:
	Rules() : cqs(Rus::get().math.rules[Ids::get().cqs]) { }
};

term::Expr* transform(term::Expr* t) {
	if (!t->rule) return t;
	if (t->rule->id == Ids::get().co &&
		t->children[1]->rule &&
		t->children[1]->rule->id == Ids::get().cdiv) {
		term::Expr* nt = new term::Expr(t->first, t->last, Rules::get().cqs);
		nt->children.push_back(t->children[0]);
		nt->children.push_back(t->children[2]);
		delete t->children[1];
		t->children.clear();
		delete t;
		t = nt;
	}
	for (auto& ch : t->children)
		ch = transform(ch);
	return t;
}

void modify_grammar(Expr& ex) {
	ex.term = transform(ex.term);
	//ex = assemble(ex);
}

void transform(Expr& ex) {
	/*if (ex.first->symb.type && ex.first != ex.last) {
		Expr e = assemble(ex);
		e.push_front(Symbol("("));
		e.push_back(Symbol(")"));
		//e.first->init = e.first->next->init;
		//e.last->final = e.last->prev->final;
		//e.first->next->init.clear();
		//e.last->prev->final.clear();
		//for (auto t : e.first->init) t->first = e.first;
		//for (auto t : e.last->final) t->last = e.last;
		ex = e;
	}*/
}

void modify_grammar(Rule* rule) {
	//transform(rule->term);
}


void modify_grammar(Assertion& ass) {
	for (auto hyp  : ass.hyps)  modify_grammar(hyp->expr);
	for (auto prop : ass.props) modify_grammar(prop->expr);
}


void modify_grammar(Def* def) {
	modify_grammar(def->ass);
	modify_grammar(def->dfm);
	modify_grammar(def->dfs);
	/*if (def->prop.first->symb != Symbol("(")) {
		def->prop.push_front(Symbol("("));
		def->prop.push_back(Symbol(")"));
	}*/
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
	Timer t;
	t.start();
	cout << "modifying grammar ... " << flush;
	for (auto n : src->theory->nodes)
		modify_grammar(n);
	t.stop();
	cout << "done in " << t << endl;
}


}} // mdl::rus


#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace {

void verify_proof(Proof* pf);

void verify_step(Step* st) {
	if (st->kind == Step::CLAIM) {
		verify_proof(st->val.prf);
		return;
	}
	Assertion* ass = st->assertion();
	//static int c = 0;
	//cout << "\tverifying step: " << c++ << " = " << show_id(ass->id) << endl;
	Substitution* ps = unify(ass->props[0]->expr, st->expr);
	if (!ps) {
		string msg = "proposition:\n";
		msg += show(*ass->props[0]) + "\n";
		msg += "ref expr:\n";
		msg += show(ass->props[0]->expr) + "\n";
		msg += show_ast(ass->props[0]->expr, true) + "\n\n";
		msg += "step:\n";
		msg += show(*st) + "\n";
		msg += show_ast(st->expr, true) + "\n\n";
		msg += "theorem " + System::get().lex.ids.toStr(st->proof->thm->ass.id) + "\n";
		throw Error("proposition unification failed", msg);
	}
	for (uint i = 0; i < ass->arity(); ++ i) {
		Substitution* hs = unify(ass->hyps[i]->expr, st->refs[i].expr());
		if (!hs) {
			string msg = "\nhypothesis:\n";
			msg += show(*ass->hyps[i]) + "\n";
			msg += "ref expr:\n";
			msg += show(st->refs[i].expr()) + "\n\n";
			msg += "step:\n";
			msg += show(*st) + "\n\n";
			msg += "theorem " + System::get().lex.ids.toStr(st->proof->thm->ass.id) + "\n";
			msg += "substitution:\n" + show(*ps) + "\n";
			delete ps;
			throw Error("hypothesis unification failed", msg);
		}
		if (!ps->join(hs)) {
			string msg = "\nhypothesis:\n";
			msg += show(*ass->hyps[i]) + "\n";
			msg += "ref expr:\n";
			msg += show(st->refs[i].expr()) + "\n\n";
			msg += "step:\n";
			msg += show(*st) + "\n\n";
			msg += "theorem " + System::get().lex.ids.toStr(st->proof->thm->ass.id) + "\n";
			msg += "prop substitution:\n" + show(*ps) + "\n";
			msg += "hyp substitution:\n" + show(*hs) + "\n";
			delete hs;
			delete ps;
			throw Error("substitution join failed", msg);
		}
		delete hs;
	}
	delete ps;
}

void verify_qed(Qed* qed) {
	if (qed->prop->expr != qed->step->expr)
		throw Error("qed prop doesn't match qed step");
}

void verify_proof(Proof* proof) {
	for (auto el : proof->elems) {
		switch (el.kind){
		case Proof::Elem::STEP: verify_step(el.val.step); break;
		case Proof::Elem::QED: verify_qed(el.val.qed); break;
		default : break;
		}
	}
}

void verify_theory(Theory* theory) {
	for (auto n : theory->nodes) {
		switch (n.kind) {
		case Node::PROOF:  verify_proof(n.val.prf); break;
		case Node::THEORY: verify_theory(n.val.thy); break;
		case Node::IMPORT: {
			Import* imp = n.val.imp;
			if (imp->primary) verify_theory(imp->source->theory);
			break;
		}
		default: break;
		}
	}
}

} // anonympus namespace

void verify(Source* source) {
	verify_theory(source->theory);
}

}} // mdl::rus

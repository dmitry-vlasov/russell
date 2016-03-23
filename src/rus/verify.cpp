#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace {

void verify_proof(Proof* pf);

void verify_step(Step* st) {
	if (st->kind == Step::CLAIM) {
		verify_proof(st->ass.prf);
		return;
	}
	Assertion* ass = st->assertion();
	Sub<>* ps = unify(ass->props[0]->expr, st->expr);
	if (!ps) throw Error("proposition unification failed");
	for (uint i = 0; i < ass->arity(); ++ i) {
		Sub<>* hs = unify(ass->hyps[i]->expr, st->refs[i].expr());
		if (!hs) {
			string msg = "\nhypothesis:\n";
			msg += show(*ass->hyps[i]) + "\n";
			msg += "step:\n";
			msg += show(*st) + "\n";
			msg += "ref expr:\n";
			msg += show(st->refs[i].expr()) + "\n";
			msg += "theorem " + Rus::get().lex.ids.toStr(st->proof->thm->ass.id) + "\n";
			msg += "substitution:\n" + show(*ps) + "\n";
			throw Error("hypothesis unification failed", msg);
		}
		if (!ps->join(hs)) {
			string msg = "\nhypothesis:\n";
			msg += show(*ass->hyps[i]) + "\n";
			msg += "step:\n";
			msg += show(*st) + "\n";
			msg += "ref expr:\n";
			msg += show(st->refs[i].expr()) + "\n";
			msg += "theorem " + Rus::get().lex.ids.toStr(st->proof->thm->ass.id) + "\n";
			msg += "prop substitution:\n" + show(*ps) + "\n";
			msg += "hyp substitution:\n" + show(*hs) + "\n";
			throw Error("substitution join failed", msg);
		}
	}
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
		if (n.kind == Node::PROOF)
			verify_proof(n.val.prf);
	}
}

} // anonympus namespace

void verify(Source* source) {
	verify_theory(&source->theory);
}

}} // mdl::rus

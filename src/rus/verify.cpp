#include <rus_ast.hpp>

namespace mdl { namespace rus { namespace {

void verify_proof(const Proof* pf);

void verify_step(const Step* st) {
	if (st->kind() == Step::CLAIM) {
		verify_proof(st->proof());
		return;
	}
	const Assertion* ass = st->ass();
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
		msg += "theorem " + Lex::toStr(st->proof()->thm->ass.id()) + "\n";
		throw Error("proposition unification failed", msg);
	}
	for (uint i = 0; i < ass->arity(); ++ i) {
		Substitution* hs = unify(ass->hyps[i]->expr, st->refs[i]->expr());
		if (!hs) {
			string msg = "\nhypothesis:\n";
			msg += show(*ass->hyps[i]) + "\n";
			msg += "ref expr:\n";
			msg += show(st->refs[i]->expr()) + "\n\n";
			msg += "step:\n";
			msg += show(*st) + "\n\n";
			msg += "theorem " + Lex::toStr(st->proof()->thm->ass.id()) + "\n";
			msg += "substitution:\n" + show(*ps) + "\n";
			delete ps;
			throw Error("hypothesis unification failed", msg);
		}
		if (!ps->join(hs)) {
			string msg = "\nhypothesis:\n";
			msg += show(*ass->hyps[i]) + "\n";
			msg += "ref expr:\n";
			msg += show(st->refs[i]->expr()) + "\n\n";
			msg += "step:\n";
			msg += show(*st) + "\n\n";
			msg += "theorem " + Lex::toStr(st->proof()->thm->ass.id()) + "\n";
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

void verify_qed(const Qed* qed) {
	if (qed->prop->expr != qed->step->expr)
		throw Error("qed prop doesn't match qed step", show(qed->prop->expr) + " != " + show(qed->step->expr));
}

void verify_proof(const Proof* proof) {
	for (auto el : proof->elems) {
		switch (el.kind){
		case Proof::Elem::STEP: verify_step(el.val.step); break;
		case Proof::Elem::QED: verify_qed(el.val.qed); break;
		default : break;
		}
	}
}

void verify_theory(const Theory* theory) {
	for (auto n : theory->nodes) {
		switch (n.kind) {
		case Node::THEORY: verify_theory(n.val.thy); break;
		case Node::IMPORT: {
			const Import* imp = n.val.imp;
			if (imp->primary) verify_theory(imp->source.get()->theory);
			break;
		}
		case Node::THEOREM: {
			const Theorem* t = n.val.thm;
			if (!t->proofs.size()) throw Error("Theorem has no proof", show_id(t->id()));
			for (const User<Proof>& p : t->proofs) verify_proof(p.get());
			break;
		}
		default: break;
		}
	}
}

} // anonympus namespace

void verify(uint src) {
	const Source* source = Sys::get().math.get<Source>().access(src);
	verify_theory(source->theory);
}

void verify() {
	for (const auto& a : Sys::mod().math.get<Assertion>()) {
		if (const Theorem* t = dynamic_cast<const Theorem*>(a.second.data)) {
			if (!t->proofs.size()) throw Error("Theorem is not proved", show_id(t->id()));
			for (const User<Proof>& p : t->proofs) verify_proof(p.get());
		}
	}
}

}} // mdl::rus

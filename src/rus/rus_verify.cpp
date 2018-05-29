#include <rus_ast.hpp>

namespace mdl { namespace rus {

void Step::verify(uint mode) const {
	if (kind() == Step::CLAIM) {
		claim()->verify(mode);
		return;
	}
	if (mode & VERIFY_SUB) {
		assert(kind() == Step::ASS);
		if (!ass()) throw Error("unknown assertion", Lex::toStr(ass_id()));
		sub = unify_forth(ass()->props[0]->expr, expr);
		if (!sub) {
			string msg = "proposition:\n";
			msg += show(*ass()->props[0]) + "\n";
			msg += "ref expr:\n";
			msg += show(ass()->props[0]->expr) + "\n";
			msg += show_ast(ass()->props[0]->expr, true) + "\n\n";
			msg += "step:\n";
			msg += show(*this) + "\n";
			msg += show_ast(expr, true) + "\n\n";
			msg += "theorem " + Lex::toStr(proof()->thm.id()) + "\n";
			throw Error("proposition unification failed", msg);
		}
		for (uint i = 0; i < ass()->arity(); ++ i) {
			Substitution hs = unify_forth(ass()->hyps[i]->expr, refs[i]->expr());
			if (!hs) {
				string msg = "\nhypothesis:\n";
				msg += show(*ass()->hyps[i]) + "\n";
				msg += "ref expr:\n";
				msg += show(refs[i]->expr()) + "\n\n";
				msg += "step:\n";
				msg += show(*this) + "\n\n";
				msg += "theorem " + Lex::toStr(proof()->thm.id()) + "\n";
				msg += "substitution:\n" + show(sub) + "\n";
				throw Error("hypothesis unification failed", msg);
			}
			if (!sub.join(hs)) {
				string msg = "\nhypothesis:\n";
				msg += show(*ass()->hyps[i]) + "\n";
				msg += "ref expr:\n";
				msg += show(refs[i]->expr()) + "\n\n";
				msg += "step:\n";
				msg += show(*this) + "\n\n";
				msg += "theorem " + Lex::toStr(proof()->thm.id()) + "\n";
				msg += "prop substitution:\n" + show(sub) + "\n";
				msg += "hyp substitution:\n" + show(hs) + "\n";
				throw Error("substitution join failed", msg);
			}
		}
	}
	if (mode & VERIFY_DISJ) {
		ass()->disj.check(sub, const_cast<Theorem*>(proof_->theorem()));
	}
}

void Qed::verify(uint mode) const {
	if ((mode & VERIFY_QED) && (prop->expr != step->expr))
		throw Error("qed prop doesn't match qed step", show(prop->expr) + " != " + show(step->expr));
}

void Proof::verify(uint mode) const {
	for (const auto& el : elems) {
		switch (kind(el)){
		case Proof::STEP: step(el)->verify(mode); break;
		case Proof::QED: qed(el)->verify(mode);  break;
		default : break;
		}
	}
}

bool Proof::check(uint mode) const {
	try {
		verify(mode);
		return true;
	} catch (Error&) {
		return false;
	}
}

void verify_theory(Theory* theory, uint mode) {
	for (auto& n : theory->nodes) {
		switch (Theory::kind(n)) {
		case Theory::THEORY: verify_theory(Theory::theory(n), mode); break;
		case Theory::THEOREM: {
			Theorem* t = Theory::theorem(n);
			if (!t->proofs.size()) {
				throw Error("Theorem has no proof", show_id(t->id()));
			}
			for (const User<Proof>& p : t->proofs) {
				if (mode & VERIFY_DISJ) {
					t->disj.dmap.clear();
				}
				p.get()->verify(mode);
			}
			break;
		}
		default: break;
		}
	}
}

void verify_source(uint src, uint mode, set<uint>& verified) {
	if (verified.count(src)) return;
	verified.insert(src);
	Source* source = Sys::mod().math.get<Source>().access(src);
	if (mode & VERIFY_DEEP) {
		for (auto& n : source->theory.nodes) {
			if (Theory::kind(n) == Theory::IMPORT) {
				verify_source(Theory::import(n)->source.id(), mode, verified);
			}
		}
	}
	verify_theory(&source->theory, mode);
}

void verify(uint src) {
	set<uint> verified;
	verify_source(src, VERIFY_SUB | VERIFY_QED | VERIFY_DISJ, verified);
}

void verify() {
	vector<const Proof*> proofs;
	for (const auto& a : Sys::mod().math.get<Assertion>()) {
		if (const Theorem* t = dynamic_cast<const Theorem*>(a.second.data)) {
			if (!t->proofs.size()) throw Error("Theorem is not proved", show_id(t->id()));
			for (const User<Proof>& p : t->proofs)
				proofs.push_back(p.get());
		}
	}
	tbb::parallel_for (tbb::blocked_range<size_t>(0, proofs.size()),
		[proofs] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i)
				proofs[i]->verify(VERIFY_SUB | VERIFY_QED);
		}
	);
	set<uint> verified;
	for (const auto& s : Sys::mod().math.get<Source>()) {
		verify_source(s.first, VERIFY_DISJ | VERIFY_DEEP, verified);
	}
}

}} // mdl::rus

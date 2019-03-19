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
			msg += ass()->props[0]->show() + "\n";
			msg += "ref expr:\n";
			msg += rus::show(ass()->props[0]->expr) + "\n";
			msg += show_ast(ass()->props[0]->expr, true) + "\n\n";
			msg += "step:\n";
			msg += show() + "\n";
			msg += show_ast(expr, true) + "\n\n";
			msg += "theorem " + Lex::toStr(proof()->thm.id()) + "\n";
			throw Error("proposition unification failed", msg);
		}
		for (uint i = 0; i < ass()->arity(); ++ i) {
			Substitution hs = unify_forth(ass()->hyps[i]->expr, refs[i]->expr());
			if (!hs) {
				string msg = "\nhypothesis:\n";
				msg += ass()->hyps[i]->show() + "\n";
				msg += "ref expr:\n";
				msg += rus::show(refs[i]->expr()) + "\n\n";
				msg += "step:\n";
				msg += show() + "\n\n";
				msg += "theorem " + Lex::toStr(proof()->thm.id()) + "\n";
				msg += "substitution:\n" + rus::show(sub) + "\n";
				throw Error("hypothesis unification failed", msg);
			}
			if (!sub.join(hs)) {
				string msg = "\nhypothesis:\n";
				msg += ass()->hyps[i]->show() + "\n";
				msg += "ref expr:\n";
				msg += rus::show(refs[i]->expr()) + "\n\n";
				msg += "step:\n";
				msg += show() + "\n\n";
				msg += "theorem " + Lex::toStr(proof()->thm.id()) + "\n";
				msg += "prop substitution:\n" + rus::show(sub) + "\n";
				msg += "hyp substitution:\n" + rus::show(hs) + "\n";
				throw Error("substitution join failed", msg);
			}
		}
	}
	if (mode & VERIFY_DISJ) {
		try {
			ass()->disj.check(sub, const_cast<Theorem*>(proof_->theorem()));
		} catch (Error& err) {
			ostringstream oss;
			ass()->disj.write(oss);
			err.msg += "assertion: " + Lex::toStr(ass()->id()) + "\n";
			err.msg += "disjointeds: " + oss.str() + "\n";
			err.msg += "substitution: " + rus::show(sub) + "\n";
			throw err;
		}
	}
}

void Qed::verify(uint mode) const {
	if ((mode & VERIFY_QED) && (prop->expr != step->expr))
		throw Error("qed prop doesn't match qed step", rus::show(prop->expr) + " != " + rus::show(step->expr));
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
					t->disj.dvars.clear();
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

#ifdef PARALLEL
#define PARALLEL_VERIFY
#endif

void verify(uint src) {
	if (src == -1) {
		vector<const Proof*> proofs;
		for (const auto& a : Sys::mod().math.get<Assertion>()) {
			if (const Theorem* t = dynamic_cast<const Theorem*>(a.second.data)) {
				if (!t->proofs.size()) throw Error("Theorem is not proved", show_id(t->id()));
				for (const User<Proof>& p : t->proofs)
					proofs.push_back(p.get());
			}
		}
#ifdef PARALLEL_VERIFY
		tbb::parallel_for (tbb::blocked_range<size_t>(0, proofs.size()),
			[proofs] (const tbb::blocked_range<size_t>& r) {
				for (size_t i = r.begin(); i != r.end(); ++i)
					proofs[i]->verify(VERIFY_SUB | VERIFY_QED);
			}
		);
#else
	for (auto p : proofs) p->verify(VERIFY_SUB | VERIFY_QED);
#endif
		set<uint> verified;
		for (const auto& s : Sys::mod().math.get<Source>()) {
			verify_source(s.first, VERIFY_DISJ | VERIFY_DEEP, verified);
		}
	} else {
		set<uint> verified;
		verify_source(src, VERIFY_SUB | VERIFY_QED | VERIFY_DISJ, verified);
	}
}

}} // mdl::rus

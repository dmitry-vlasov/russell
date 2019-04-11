#include "rus_prover_multy_subst.hpp"
#include "index/rus_prover_index_unify.hpp"

namespace mdl { namespace rus { namespace prover {

MultySubst::MultySubst(const vector<const Subst*>& subs) {
	for (auto s : subs) {
		add(s);
	}
}
Subst MultySubst::makeSubs(Subst& unif) const {
	Subst ret;
	for (const auto& p : msub_) {
		Term term = index::unify_general(p.second, unif);
		if (term.empty()) {
			return Subst(false);
		}
		ret.compose(p.first, term);
		if (!ret.ok()) {
			break;
		}
	}
	return ret;
}

void MultySubst::add(const Subst* sub) {
	for (const auto& p : *sub) {
		msub_[p.first].push_back(p.second);
	}
}

void sub_closure(Subst& sub) {
	enum { WATCHDOG_THRESHOLD = 32 };
	uint watchdog = 0;
	while (sub.composeable(sub)) {
		if (watchdog++ > WATCHDOG_THRESHOLD) {
			cout << "SOMETHING WRONG: too much deep substitution closure" << endl;
			break;
		}
		if (!sub.compose(sub)) {
			break;
		}
	}
}

Subst unify_subs(const MultySubst& t) {
	Subst unif;
	Subst gen = t.makeSubs(unif);
	return unify_subs(unif, gen);
}

Subst unify_subs(Subst unif, Subst gen) {
	if (!(gen.ok() && unif.ok())) {
		return Subst(false);
	}
	if (!gen.intersects(unif)) {
		if (gen.compose(unif)) {
			sub_closure(gen);
			return gen;
		} else {
			return Subst(false);
		}
	} else {
		MultySubst msub({&unif, &gen});
		return unify_subs(msub);
	}
}

string show(const MultyUnifiedSubs& ms) {
	ostringstream oss;
	for (const auto& p : ms) {
		oss << show(p.first) << ":" << endl;
		oss << Indent::paragraph(p.second.show()) << endl;
	}
	return oss.str();
}

}}}

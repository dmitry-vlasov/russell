#include "../rus_prover_cartesian.hpp"
#include "../rus_prover_limit.hpp"
#include "rus_prover_unify_matrix.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

MultyUnifiedSubs unify_subs_matrix(Prop* pr, Hyp* hy, const vector<ProofExpIndexed>& hs, const ProofsSizeLimit* limit) {
	Matrix mi(pr, hy, hs, limit);
	if (mi.empty()) {
		return MultyUnifiedSubs();
	}
	MultyUnifiedSubs ret;
	try {
		MultyUnifiedSubs unif;
		MultyUnifiedSubs gen = mi.compute(unif);
		for (const auto& p : unif) {
			Subst sub = unify_subs(p.second, gen[p.first]);
			if (sub.ok()) {
				Subst delta = pr->sub;
				if (delta.compose(sub)) {
					ret[p.first] = delta;
				}
			}
		}
	} catch (std::exception& e) {
		cout << e.what() << endl;
		cout << mi.show() << endl;
		throw e;
	}
	return ret;
}

MultyUnifiedSubs unify_subs_matrix(const Subst& common, const vector<vector<SubstInd>>& matr, const ProofsSizeLimit* limit) {
	Matrix mi(matr, limit);
	if (mi.empty()) {
		return MultyUnifiedSubs();
	}
	MultyUnifiedSubs ret;
	try {
		MultyUnifiedSubs unif;
		MultyUnifiedSubs gen = mi.compute(unif);
		for (const auto& p : unif) {
			Subst sub = unify_subs(p.second, gen[p.first]);
			if (sub.ok()) {
				Subst delta = common;
				if (delta.compose(sub)) {
					ret[p.first] = delta;
				}
			}
		}
	} catch (std::exception& e) {
		cout << e.what() << endl;
		cout << mi.show() << endl;
		throw e;
	}
	return ret;
}

Term unify_general(const vector<Term>& ex, Subst& sub) {
	vector<const Term*> terms;
	for (const auto& e : ex) {
		terms.emplace_back(&e);
	}
	try {
		map<vector<uint>, TermSubst> unif = unify_general(terms);
		if (!unif.size()) {
			sub.spoil();
			return Term();
		} else if (unif.size() == 1) {
			if (unif.begin()->second.sub.ok()) {
				Subst common = unify_subs(unif.begin()->second.sub, sub);
				if (common.ok()) {
					sub = std::move(common);
					return sub.apply(unif.begin()->second.term);
				} else {
					sub.spoil();
					return Term();
				}
			} else {
				sub.spoil();
				return Term();
			}
		} else {
			throw Error("more then 1 unification result");
		}
	} catch (Error& err) {
		cout << "unify_general error: " << endl;
		for (const auto& e : ex) {
			cout << "\t" << e.show() << endl;
		}
		throw err;
	}
}

}}}}

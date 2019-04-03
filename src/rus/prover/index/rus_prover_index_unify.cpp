#include "../rus_prover_cartesian.hpp"
#include "rus_prover_index_matrix.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

bool debug_trie_matrix = false;

void unify_subs(Matrix& mi, const Prop* pr, MultyUnifiedSubs& ret) {
	MultyUnifiedSubs unif;
	MultyUnifiedSubs gen = mi.compute(unif);
	for (const auto& p : unif) {
		Subst sub = unify_subs(p.second, gen[p.first]);
		if (sub.ok()) {
			Subst delta = pr->sub;
			delta.compose(sub);
			ret[p.first] = delta;
		}
	}
}

MultyUnifiedSubs unify_subs_matrix(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs) {
	Matrix mi(pr, hy, hs);
	if (mi.empty()) {
		return MultyUnifiedSubs();
	}
	MultyUnifiedSubs ret;
	try {
		unify_subs(mi, pr, ret);
	} catch (std::exception& e) {
		//cout << "MATRIX no. " << c << endl;
		cout << mi.show() << endl;
		throw e;
	}
	return ret;
}

bool debug_unify_general = false;

Term unify_general(const vector<Term>& ex, Subst& sub) {
	vector<MultyIter> iters;
	for (const auto& e : ex) {
		iters.emplace_back(Term::TermIter(e));
	}
	try {
		map<vector<uint>, FlatTermSubst> unif = unify_general(iters);
		if (!unif.size()) {
			sub.spoil();
			return Term();
		} else if (unif.size() == 1) {
			if (unif.begin()->second.sub->ok()) {
				Subst common = unify_subs(*unif.begin()->second.sub, sub);
				if (common.ok()) {
					sub = common;
					return apply(common, *unif.begin()->second.term);
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
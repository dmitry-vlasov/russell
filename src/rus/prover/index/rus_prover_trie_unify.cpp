#include "../rus_prover_cartesian.hpp"
#include "rus_prover_matrix_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

bool debug_trie_matrix = false;

void unify_subs(MatrixIndex& mi, const Prop* pr, MultyUnifiedSubs& ret) {
	MultyUnifiedSubs unif;
	MultyUnifiedSubs gen = mi.compute(unif);

	if (debug_trie_index) {
		cout << "gen.size(): " << gen.size() << endl;
		cout << "unif.size(): " << unif.size() << endl;
	}

	for (const auto& p : unif) {
		Subst sub = unify_subs(p.second, gen[p.first]);
		if (sub.ok()) {
			Subst delta = pr->sub;
			delta.compose(sub);
			ret[p.first] = delta;
		} else if (debug_trie_index) {
			cout << "sub: " << sub.show() << " rejected" << endl;
			cout << "p.second: " << p.second.show() << endl;
			cout << "gen[p.first]: " << gen[p.first].show() << endl;
			debug_unify_subs_func = true;
			unify_subs(p.second, gen[p.first]);
		}
	}
}

MultyUnifiedSubs unify_subs_matrix(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs) {

	static int c = 0;
	c++;
	//debug_trie_matrix = (c == 3);
	if (debug_trie_matrix) {
		cout << "AAA" << endl;
	}
	MatrixIndex mi(pr, hy, hs);
	if (mi.empty()) {
		return MultyUnifiedSubs();
	}

	/*cout << "MATRIX no. " << c << ", dim: " << mi.dim_vars() << "x" << mi.dim_hyp() << ", card: " << mi.card_str() << endl;
	if (debug_trie_matrix) {
		cout << "MATRIX no. " << c <<  ", card: " << mi.card_str() << endl ;
		cout << mi.show() << endl;
	}*/

	MultyUnifiedSubs ret;
	try {
		unify_subs(mi, pr, ret);
	} catch (Error& err) {
		debug_trie_matrix = true;
		cout << "MATRIX no. " << c << endl;
		cout << mi.show() << endl;
		//return unify_subs(mi, pr);
		throw err;
	} catch (std::exception& e) {
		debug_trie_matrix = true;
		cout << "MATRIX no. " << c << endl;
		cout << mi.show() << endl;
		unify_subs(mi, pr, ret);
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

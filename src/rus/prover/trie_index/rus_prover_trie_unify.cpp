#include "../rus_prover_cartesian.hpp"
#include "rus_prover_trie_matrix_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

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
			cout << "sub: " << prover::show(sub) << " rejected" << endl;
			cout << "p.second: " << prover::show(p.second) << endl;
			cout << "gen[p.first]: " << prover::show(gen[p.first]) << endl;
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

}}}}

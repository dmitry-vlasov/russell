#include "rus_prover_down.hpp"
#include "rus_prover_cartesian.hpp"
#include "tree_index/rus_prover_matrix_index.hpp"
#include "trie_index/rus_prover_trie_matrix.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_unify_subs = false;
vector<uint> error_inds;

void unify_subs_sequent(Prop* pr, Hyp* hy, ProofHypIndexed hi, MultyUnifiedSubs& ret) {
	CartesianIter ind;
	const ProofHyp* h = hi.proof;
	for (auto& x : pr->premises) {
		if (x.get() != hy) {
			ind.addDim(x->proofs.size());
		} else {
			ind.addFixed(x->proofs.size(), hi.ind);
		}
	}
	if (ind.card() == 0) {
		return;
	}
	while (true) {
		vector<const Subst*> subs;
		bool show_debug = debug_unify_subs && (!error_inds.size() || error_inds == ind.inds());
		if (show_debug) {
			cout << "CURRENT: " << ind.current() << endl;
			cout << "UNIFYING: \n--------------" << endl;
			cout << "PROP: " << pr->ind << endl;
		}
		for (uint i = 0; i < ind.size(); ++ i) {
			ProofHyp* ph = pr->premises[i].get()->proofs[ind[i]].get();
			if (show_debug) {
				cout << ph->ind << ": " << show(ph->expr) << endl;
				cout << "sub:" << endl;
				cout << Indent::paragraph(show(ph->sub)) << endl;
			}
			subs.push_back(&ph->sub);
		}
		if (show_debug) {
			cout << "-------------" << endl;
			debug_unify_subs_func = true;
		}
		Subst sub = unify_subs(MultySubst(subs));
		if (sub.ok) {
			Subst delta = pr->sub;
			if (show_debug) {
				cout << "DELTA" << endl;
				cout << show(delta) << endl;
				cout << "SUB" << endl;
				cout << show(sub) << endl;
			}
			delta.compose(sub);
			ret[ind.inds()] = delta;
		}
		debug_unify_subs_func = false;
		if (!ind.hasNext()) {
			break;
		}
		ind.makeNext();
	}
}

uint unification_space_card(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs) {
	uint ret = 1;
	for (auto& x : pr->premises) {
		if (x.get() != hy) {
			ret *= x->proofs.size();
		} else {
			ret *= hs.size();
		}
	}
	return ret;
}

string unification_space_card_str(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs) {
	string ret;
	bool first = true;
	for (auto& x : pr->premises) {
		if (!first) {
			ret += " x ";
		}
		if (x.get() != hy) {
			ret += to_string(x->proofs.size());
		} else {
			ret += to_string(hs.size());
		}
		first = false;
	}
	ret += " = " + to_string(unification_space_card(pr, hy, hs));
	return ret;
}

MultyUnifiedSubs unify_subs_sequent(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs) {
	MultyUnifiedSubs ret;
	for (auto h : hs) {
		unify_subs_sequent(pr, hy, h, ret);
	}
	return ret;
}

bool similar_subs_1(const Subst& s1, const Subst& s2) {
	if (s1 == s2) return true;
	Subst unif = unify_subs(MultySubst({&s1, &s2}));
	if (!unif.ok) {
		//don't unify
		return false;
	}
	for (const auto& p : unif.sub) {
		if (p.second.kind() != LightTree::VAR) {
			// is not a var replacement
			return false;
		}
	}
	return true;
}

bool similar_subs(const Subst& s1, const Subst& s2) {
	if (s1 == s2) return true;
	Subst s1_vars_inv;
	Subst s1_terms;
	for (const auto& p : s1.sub) {
		if (p.second.kind() == LightTree::VAR && !s2.sub.count(p.first)) {
			s1_vars_inv.sub[p.second.var()] = LightTree(p.first);
		} else {
			s1_terms.sub[p.first] = p.second;
		}
	}
	s1_terms.compose(s1_vars_inv);
	return s2 == s1_terms;
}

bool compare_unified_subs(const MultyUnifiedSubs& ms1, const MultyUnifiedSubs& ms2) {
	if (ms1.size() != ms2.size()) {
		return false;
	}
	for (const auto p1 : ms1) {
		if (!ms2.count(p1.first)) {
			return false;
		}
		if (!similar_subs(p1.second, ms2.at(p1.first))) {
			return false;
		}
	}
	for (const auto p2 : ms2) {
		if (!ms1.count(p2.first)) {
			return false;
		}
		if (!similar_subs(p2.second, ms1.at(p2.first))) {
			return false;
		}
	}
	return true;
}

string unified_subs_diff(const MultyUnifiedSubs& ms1, const MultyUnifiedSubs& ms2) {
	string ret;
	if (ms1.size() != ms2.size()) {
		ret += "sequential.size() = " + to_string(ms1.size()) + " != " + to_string(ms2.size()) + " = matrix.size()\n";
	}
	for (const auto p1 : ms1) {
		if (!ms2.count(p1.first)) {
			ret += "matrix doesn't have key" + show(p1.first) + "\n";
			ret += "sequential value:\n";
			ret += Indent::paragraph(show(p1.second));
		} else if (p1.second != ms2.at(p1.first)) {
			ret += "sequential and matrix values for key" + show(p1.first) + " differ\n";
			ret += "sequential value:\n";
			ret += Indent::paragraph(show(p1.second));
			ret += "matrix value:\n";
			ret += Indent::paragraph(show(ms2.at(p1.first)));
		}
	}
	for (const auto p2 : ms2) {
		if (!ms1.count(p2.first)) {
			ret += "sequential doesn't have key" + show(p2.first) + "\n";
			ret += "matrix value:\n";
			ret += Indent::paragraph(show(p2.second));
		}
	}
	return ret;
}

vector<Node*> unify_down(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs) {

	static int c = 0;
	c++;
	cout << "Matrix no. " << c << ", card: " << unification_space_card_str(pr, hy, hs) << endl;

	Timer timer; timer.start();
	MultyUnifiedSubs unified_subs_1 = unify_subs_sequent(pr, hy, hs);
	timer.stop();
	cout << "sequntial unification: " << timer << endl;
	cout << "results with " << unified_subs_1.size() << " variants " << endl << endl;

	timer.clear();
	timer.start();
	MultyUnifiedSubs unified_subs_2 = trie_index::unify_subs_matrix(pr, hy, hs);
	timer.stop();
	cout << "matrix unification: " << timer << endl;
	cout << "results with " << unified_subs_2.size() << " variants " << endl << endl << endl;

	if (!compare_unified_subs(unified_subs_1, unified_subs_2)) {
		cout << "SUB UNIFICATION DIFF" << endl;
		//cout << "SEQUENTIAL:" << endl;
		//cout << show(unified_subs_1) << endl;
		//cout << "MATRIX:" << endl;
		//cout << show(unified_subs_2) << endl;
		cout << "DIFF:" << endl;
		cout << unified_subs_diff(unified_subs_1, unified_subs_2) << endl;
		cout << trie_index::MatrixIndex(pr, hy, hs).show() << endl;

		//trie_index::debug_flat_apply = true;
 		trie_index::debug_trie_index = true;
 		//trie_index::debug_flatterm = true;
		trie_index::unify_subs_matrix(pr, hy, hs);

		//debug_unify_subs = true;
		//unify_subs_sequent(pr, h);
		throw Error("SUB UNIFICATION DIFF");
	} else {
		//cout << "SUB UNIFICATION EQUAL" << endl;
	}

	for (const auto& p : unified_subs_1) {
		vector<uint> ind = p.first;
		vector<ProofHyp*> ch;
		for (uint i = 0; i < ind.size(); ++ i) {
			ProofHyp* ph = pr->premises[i].get()->proofs[ind[i]].get();
			ch.push_back(ph);
		}
		try {
			ProofProp* pp = new ProofProp(*pr, ch, p.second);
			for (auto& h : pr->proofs) {
				if (pp->equal(h.get())) {
					cout << "DUPLICATE PROP PROOF" << endl;
					cout << pp->show() << endl;
					cout << "-----------" << endl;
					cout << h->show() << endl;
				}
			}
			pr->proofs.emplace_back(pp);
		} catch (Error& err) {
			string msg;
			msg += "while unifying down:\n";
			for (auto c : ch) {
				msg += show(c->sub) + "\n";
			}
			err.msg += "\n" + msg;
			err.msg += "\nunifier: " + show(p.second);
			error_inds = ind;
			debug_unify_subs = true;
			unify_subs_sequent(pr, hy, hs);
			throw err;
		}
	}
	if (unified_subs_1.size()) {
		return {pr};
	} else {
		return vector<Node*>();
	}
}

}}}


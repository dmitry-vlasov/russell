#include "rus_prover_down.hpp"
#include "rus_prover_cartesian.hpp"
#include "rus_prover_vector_index.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_unify_subs = false;

MultyUnifiedSubs unify_subs_matrix(Prop* pr, const vector<const ProofHyp*>& hs);

void unify_subs_sequent(Prop* pr, const ProofHyp* h, MultyUnifiedSubs& ret) {
	CartesianIter ind;
	for (auto& x : pr->premises) {
		if (x.get() != &h->node) {
			ind.addDim(x->proofs.size());
		} else {
			ind.addFixed(x->proofs.size(), find_in_vector(x->proofs, h));
		}
	}
	if (ind.card() == 0) {
		return;
	}
	while (true) {
		vector<const Subst*> subs;
		if (debug_unify_subs) {
			cout << "CURRENT: " << ind.current() << endl;
			cout << "UNIFYING: \n--------------" << endl;
			cout << "PROP: " << pr->ind << endl;
		}
		for (uint i = 0; i < ind.size(); ++ i) {
			ProofHyp* ph = pr->premises[i].get()->proofs[ind[i]].get();
			if (debug_unify_subs) {
				cout << ph->ind << ": " << show(ph->expr) << endl;
				cout << "sub:" << endl;
				cout << Indent::paragraph(show(ph->sub)) << endl;
			}
			subs.push_back(&ph->sub);
		}
		if (debug_unify_subs) {
			cout << "-------------" << endl;
		}
		Subst sub = unify_subs(MultySubst(subs));
		if (sub.ok) {
			Subst delta = pr->sub;
			delta.compose(sub);
			ret[ind.inds()] = delta;
		}
		if (!ind.hasNext()) {
			break;
		}
		ind.makeNext();
	}
}

MultyUnifiedSubs unify_subs_sequent(Prop* pr, const vector<const ProofHyp*>& hs) {
	MultyUnifiedSubs ret;
	for (auto h : hs) {
		unify_subs_sequent(pr, h, ret);
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
		ret += "ms1.size() = " + to_string(ms1.size()) + " != " + to_string(ms2.size()) + " = ms2.size()\n";
	}
	for (const auto p1 : ms1) {
		if (!ms2.count(p1.first)) {
			ret += "ms2 doesn't have key" + show(p1.first) + "\n";
		} else if (p1.second != ms2.at(p1.first)) {
			ret += "ms1 and m2 values for key" + show(p1.first) + " differ\n";
			ret += "ms1 value:\n";
			ret += Indent::paragraph(show(p1.second));
			ret += "ms2 value:\n";
			ret += Indent::paragraph(show(ms2.at(p1.first)));
		}
	}
	for (const auto p2 : ms2) {
		if (!ms1.count(p2.first)) {
			ret += "ms1 doesn't have key" + show(p2.first) + "\n";
		} else if (p2.second != ms1.at(p2.first)) {
			ret += "ms1 and m2 values for key" + show(p2.first) + " differ\n";
			ret += "ms2 value:\n";
			ret += Indent::paragraph(show(p2.second));
			ret += "ms1 value:\n";
			ret += Indent::paragraph(show(ms1.at(p2.first)));
		}
	}
	return ret;
}

vector<Node*> unify_down(Prop* pr, const vector<const ProofHyp*>& h) {
	Timer timer; timer.start();
	MultyUnifiedSubs unified_subs_1 = unify_subs_sequent(pr, h);
	timer.stop();
	cout << "sequntial unification: " << timer << endl;

	timer.clear();
	timer.start();
	MultyUnifiedSubs unified_subs_2 = unify_subs_matrix(pr, h);
	timer.stop();
	cout << "matrix unification: " << timer << endl;

	if (!compare_unified_subs(unified_subs_1, unified_subs_2)) {
		cout << "SUB UNIFICATION DIFF" << endl;
		cout << "SEQUENTIAL:" << endl;
		cout << show(unified_subs_1) << endl;
		cout << "MATRIX:" << endl;
		cout << show(unified_subs_2) << endl;
		cout << "DIFF:" << endl;
		cout << unified_subs_diff(unified_subs_1, unified_subs_2) << endl;

 		debug_multy_index = true;
		unify_subs_matrix(pr, h);

		//debug_unify_subs = true;
		//unify_subs_sequent(pr, h);
		throw Error("SUB UNIFICATION DIFF");
	} else {
		cout << "SUB UNIFICATION EQUAL" << endl;
	}

	for (const auto& p : unified_subs_1) {
		vector<uint> ind = p.first;
		vector<ProofHyp*> ch;
		for (uint i = 0; i < ind.size(); ++ i) {
			ProofHyp* ph = pr->premises[i].get()->proofs[ind[i]].get();
			ch.push_back(ph);
		}
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
	}
	if (unified_subs_1.size()) {
		return {pr};
	} else {
		return vector<Node*>();
	}
}

}}}


#include "rus_prover_down.hpp"
#include "rus_prover_multy_index.hpp"
#include "rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_unify_subs = false;

MultyUnifiedSubs unify_substitutions(Prop* pr, const ProofHyp* h) {
	CartesianIter ind;
	for (auto& x : pr->premises) {
		if (x.get() != &h->node) {
			ind.addDim(x->proofs.size());
		} else {
			ind.addFixed(x->proofs.size(), find_in_vector(x->proofs, h));
		}
	}
	MultyUnifiedSubs ret;
	if (ind.card() == 0) {
		return ret;
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
	return ret;
}

vector<Node*> unify_down(Prop* pr, const ProofHyp* h) {
	MultyUnifiedSubs unified_subs = unify_substitutions(pr, h);
	for (const auto& p : unified_subs) {
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
	if (unified_subs.size()) {
		return {pr};
	} else {
		return vector<Node*>();
	}
}

}}}


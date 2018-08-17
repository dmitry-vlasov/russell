#include "rus_prover_cartesian.hpp"
#include "rus_prover_down.hpp"
#include "rus_prover_multy_index.hpp"

namespace mdl { namespace rus { namespace prover {

struct MatrixIndex {
	MatrixIndex(uint hd) : dim_hyp(hd) { }

	void addProofs(const Hyp::Proofs& proofs, uint i) {
		for (const auto& p : proofs) {
			const Subst& s = p->sub;
			for (const auto& x : s.sub) {
				if (!mindex_.count(x.first)) {
					mindex_[x.first] = vector<Index>(dim_hyp);
				}
				mindex_[x.first][i].add(x.second);
			}
		}
	}

	MultyUnifiedSubs compute(MultyUnifiedSubs& unif) {
		MultyUnifiedSubs s;
		for (const auto& p : mindex_) {
			vector<const Index*> x;
			for (auto& i : p.second) {
				x.push_back(&i);
			}
			MultyUnifiedTerms terms = unify(x, unif, nullptr);
			for (const auto& t : terms) {
				s[t.first].sub[p.first] = terms[t.first];
			}
		}
		return s;
	}

private:
	uint dim_hyp;
	map<LightSymbol, vector<Index>> mindex_;
};

MultyUnifiedSubs unify_subs(MatrixIndex& mi) {
	MultyUnifiedSubs ret;
	MultyUnifiedSubs unif;
	MultyUnifiedSubs gen = mi.compute(unif);
	for (const auto& p : unif) {
		ret[p.first] = unify_subs(p.second, gen[p.first]);
	}
	return ret;
}

vector<Node*> unify_down_2(Prop* pr, const ProofHyp* h) {
	uint arity = pr->premises.size();
	MatrixIndex mi(arity);
	for (uint i = 0; i < arity; ++ i) {
		if (!pr->premises[i]->proofs.size()) {
			return vector<Node*>();
		}
		mi.addProofs(pr->premises[i]->proofs, i);
	}
	bool new_proofs = false;
	MultyUnifiedSubs subs = unify_subs(mi);
	for (const auto& p : subs) {
		if (!p.second.ok) {
			continue;
		}
		vector<ProofHyp*> ch;
		for (uint i = 0; i < arity; ++ i) {
			ProofHyp* ph = pr->premises[i].get()->proofs[p.first[i]].get();
			ch.push_back(ph);
		}
		Subst delta = pr->sub;
		delta.compose(p.second);
		ProofProp* pp = new ProofProp(*pr, ch, delta);
		for (auto& h : pr->proofs) {
			if (pp->equal(h.get())) {
				cout << "DUPLICATE PROP PROOF" << endl;
				cout << pp->show() << endl;
				cout << "-----------" << endl;
				cout << h->show() << endl;
			}
		}
		pr->proofs.emplace_back(pp);
		new_proofs = true;
	}

	if (new_proofs) {
		return {pr};
	} else {
		return vector<Node*>();
	}
}

}}}


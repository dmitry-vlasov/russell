#include "rus_prover_cartesian.hpp"
#include "rus_prover_down.hpp"
#include "rus_prover_matrix_index.hpp"

namespace mdl { namespace rus { namespace prover {

void MatrixIndex::addProofs(const Hyp::Proofs& proofs, uint i) {
	for (uint j = 0; j < proofs.size(); ++j) {
		auto p = proofs[j].get();
		const Subst& s = p->sub;
		for (const auto& x : s.sub) {
			if (!mindex_.count(x.first)) {
				mindex_[x.first] = vector<IndexInt>(dim_hyp);
			}
			mindex_[x.first][i].add(x.second, j);
		}
	}
}
void MatrixIndex::addProof(const ProofHyp* p, uint i, uint j) {
	const Subst& s = p->sub;
	for (const auto& x : s.sub) {
		if (!mindex_.count(x.first)) {
			mindex_[x.first] = vector<IndexInt>(dim_hyp);
		}
		mindex_[x.first][i].add(x.second, j);
	}
}

MultyUnifiedSubs MatrixIndex::compute(MultyUnifiedSubs& unif) {
	MultyUnifiedSubs s;
	for (const auto& p : mindex_) {
		VectorIndex vectIndex;
		for (auto& i : p.second) {
			vectIndex.add(i);
		}
		if (debug_multy_index) {
			cout << "MultyUnifiedSubs compute(MultyUnifiedSubs& unif)" << endl;
		}
		MultyUnifiedTerms terms = unify(vectIndex, unif, nullptr);
		for (const auto& t : terms) {
			if (debug_multy_index) {
				cout << prover::show(t.first) << " --> term: " << prover::show(terms[t.first]) << endl;
			}
			s[t.first].sub[p.first] = terms[t.first];
		}
	}
	return s;
}

string MatrixIndex::show() const {
	string ret;
	ret += "DIMENSION: " + to_string(mindex_.size()) + "\n";
	for (const auto& p : mindex_) {
		ret += "\nVAR: " + prover::show(p.first) + "\n";
		ret += "==============================\n";
		for (uint i = 0; i < p.second.size(); ++ i) {
			ret += "index: " + to_string(i) + "\n";
			ret += p.second[i].show() + "\n";
			ret += "-----------------------------\n\n";
		}
	}
	return ret;
}

MultyUnifiedSubs unify_subs(MatrixIndex& mi) {
	MultyUnifiedSubs ret;
	MultyUnifiedSubs unif;
	MultyUnifiedSubs gen = mi.compute(unif);
	for (const auto& p : unif) {
		ret[p.first] = unify_subs(p.second, gen[p.first]);
	}
	return ret;
}

MultyUnifiedSubs unify_subs_matrix(Prop* pr, const ProofHyp* h) {
	uint arity = pr->premises.size();
	MatrixIndex mi(arity);
	for (uint i = 0; i < arity; ++ i) {
		const auto& proofs = pr->premises[i]->proofs;
		if (!proofs.size()) {
			return MultyUnifiedSubs();
		}
		if (pr->premises[i].get() != &h->node) {
			mi.addProofs(proofs, i);
		} else {
			mi.addProof(h, i, find_in_vector(proofs, h));
		}
	}

	static int c = 0;
	c++;
	if (debug_multy_index) {
		cout << "MATRIX no. " << c << endl;
		cout << mi.show() << endl;
	}

	return unify_subs(mi);}

}}}


#include "rus_prover_cartesian.hpp"
#include "rus_prover_down.hpp"
#include "rus_prover_matrix_index.hpp"

namespace mdl { namespace rus { namespace prover {

void MatrixIndex::addProofs(const Hyp::Proofs& proofs, uint i) {
	proofSizes_[i] = proofs.size();
	for (uint j = 0; j < proofs.size(); ++j) {
		auto p = proofs[j].get();
		for (const auto& x : p->sub.sub) {
			if (!mindex_.count(x.first)) {
				mindex_[x.first] = vector<IndexInt>(dim_hyp);
			}
			mindex_[x.first][i].add(x.second, j);
		}
	}
}

void MatrixIndex::addProof(const ProofHyp* p, uint i, uint j) {
	proofSizes_[i] = 1;
	for (const auto& x : p->sub.sub) {
		if (!mindex_.count(x.first)) {
			mindex_[x.first] = vector<IndexInt>(dim_hyp);
		}
		mindex_[x.first][i].add(x.second, j);
	}
}

MultyUnifiedTerms multiply(const MultyUnifiedTerms& terms, const vector<uint>& factors) {
	CartesianProd<uint> mult_prod;
	for (auto size : factors) {
		if (size != -1) {
			mult_prod.incSize();
			for (uint i = 0; i < size; ++ i) {
				mult_prod.incDim(i);
			}
		}
	}
	MultyUnifiedTerms ret;
	for (const auto& p : terms) {
		vector<uint> part_leafs = p.first;
		while (true) {
			vector<uint> complete_leafs(factors.size(), -1);
			vector<uint> mult_leafs = mult_prod.data();
			for (uint i = 0, j = 0, k = 0; i < factors.size(); ++ i) {
				if (factors[i] == -1) {
					complete_leafs[i] = part_leafs[j++];
				} else {
					complete_leafs[i] = mult_leafs[k++];
				}
			}

			//cout << "complete_leafs = " << show(complete_leafs) << endl;

			ret[complete_leafs] = p.second;
			if (!mult_prod.hasNext()) {
				break;
			}
			mult_prod.makeNext();
		}
	}
	return ret;
}

MultyUnifiedSubs MatrixIndex::compute(MultyUnifiedSubs& unif) {
	map<LightSymbol, MultyUnifiedTerms> terms;
	for (const auto& p : mindex_) {
		VectorIndex vectIndex;
		vector<uint> factors;
		for (uint i = 0; i < dim_hyp; ++i) {
			const auto& ind = p.second[i];
			if (ind.index().size) {
				vectIndex.add(ind, proofSizes_[i]);
				factors.push_back(-1);
			} else {
				factors.push_back(proofSizes_[i]);
			}
		}
		terms[p.first] = multiply(unify(vectIndex, unif), factors);
		if (debug_multy_index) {
			cout << "unified terms for: " << prover::show(p.first) << endl;
			cout << Indent::paragraph(prover::show(terms[p.first])) << endl;
			cout << "unifier:" << endl;
			cout << Indent::paragraph(prover::show(unif)) << endl;
		}
	}
	set<vector<uint>> common;
	for (const auto& p : terms.begin()->second) {
		bool is_common = true;
		for (const auto& q : terms) {
			if (!q.second.count(p.first)) {
				cout << "non common = " << prover::show(p.first) << endl;
				is_common = false;
				break;
			}
		}
		if (is_common) {
			cout << "common = " << prover::show(p.first) << endl;
			common.insert(p.first);
		}
	}
	MultyUnifiedSubs s;
	for (const auto& c : common) {
		for (const auto& p : terms) {
			if (debug_multy_index) {
				cout << prover::show(c) << " --> term: " << prover::show(p.second.at(c)) << endl;
			}
			s[c].sub[p.first] = p.second.at(c);
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
	debug_multy_index = (c == 2);
	if (debug_multy_index) {
		cout << "MATRIX no. " << c << endl;
		cout << mi.show() << endl;
	}

	return unify_subs(mi);
}

}}}


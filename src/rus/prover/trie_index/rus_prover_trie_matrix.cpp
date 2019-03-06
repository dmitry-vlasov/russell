#include "../rus_prover_cartesian.hpp"
#include "../rus_prover_down.hpp"
#include "rus_prover_trie_matrix.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

bool debug_trie_matrix = false;

static void addProofs(map<LightSymbol, unique_ptr<VectorIndex>>& mindex_, vector<vector<uint>>& proofInds_, uint dim_hyp_, const Hyp::Proofs& proofs, uint i) {
	proofInds_[i] = vector<uint>(proofs.size());
	for (uint j = 0; j < proofs.size(); ++j) {
		auto p = proofs[j].get();
		for (const auto& x : p->sub.sub) {
			if (!mindex_.count(x.first)) {
				mindex_.emplace(x.first, new VectorIndex(dim_hyp_));
			}
			mindex_.at(x.first)->vect[i]->add(x.second, j);
		}
		proofInds_[i][j] = j;
	}
}

static void addProofs(map<LightSymbol, unique_ptr<VectorIndex>>& mindex_, vector<vector<uint>>& proofInds_, uint dim_hyp_, const vector<ProofHypIndexed>& hs, uint i) {
	proofInds_[i] = vector<uint>(hs.size());
	for (uint j = 0; j < hs.size(); ++j) {
		ProofHypIndexed hi = hs[j];
		for (const auto& x : hi.proof->sub.sub) {
			if (!mindex_.count(x.first)) {
				mindex_.emplace(x.first, new VectorIndex(dim_hyp_));
			}
			mindex_.at(x.first)->vect[i]->add(x.second, hi.ind);
		}
		proofInds_[i][j] = hi.ind;
	}
}

MatrixIndex::MatrixIndex(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs) :
	dim_hyp_(pr->premises.size()), proofInds_(dim_hyp_), empty_(false) {
	for (uint i = 0; i < dim_hyp_; ++ i) {
		const auto& proofs = pr->premises[i]->proofs;
		if (proofs.empty()) {
			empty_ = true;
			break;
		}
		if (pr->premises[i].get() != hy) {
			addProofs(mindex_, proofInds_, dim_hyp_, proofs, i);
		} else {
			addProofs(mindex_, proofInds_, dim_hyp_, hs, i);
		}
	}
	for (auto& p : mindex_) {
		for (uint i = 0; i < dim_hyp_; ++i) {
			p.second->vect[i]->init(proofInds_[i]);
		}
	}
}

uint MatrixIndex::card() const {
	uint ret = 1;
	for (const auto& p : proofInds_) {
		ret *= p.size();
	}
	return ret;
}

string MatrixIndex::card_str() const {
	string ret;
	bool first = true;
	for (const auto& p : proofInds_) {
		if (!first) {
			ret += " x ";
		}
		ret += to_string(p.size());
		first = false;
	}
	ret += " = " + to_string(card());
	return ret;
}

uint matrix_vector_counter = 0;

MultyUnifiedSubs MatrixIndex::compute(MultyUnifiedSubs& unif) {
	if (mindex_.empty()) {
		CartesianProd<uint> proofs_prod;
		for (uint i = 0; i < dim_hyp_; ++ i) {
			proofs_prod.addDim(proofInds_[i]);
		}
		while (true) {
			vector<uint> proof_inds = proofs_prod.data();
			unif[proof_inds];
			if (!proofs_prod.hasNext()) {
				break;
			}
			proofs_prod.makeNext();
		}
		return MultyUnifiedSubs();
	}
	map<LightSymbol, VectorUnified> unified_columns;
	matrix_vector_counter = 0;
	for (auto& p : mindex_) {
		try {
			unified_columns[p.first] = std::move(p.second->unify_general());
		} catch (Error& err) {
			cout << "while unifying matrix var: " << prover::show(p.first) << endl;
			throw err;
		}
		//cout << "var " << prover::show(p.first) << " has " << terms[p.first].map().size() << " unified" << endl;
		matrix_vector_counter += 1;
	}
	return intersect(unified_columns, unif);
}

string MatrixIndex::show() const {
	if (empty_) {
		return "empty\n";
	}
	string ret;
	ret += "DIMENSION: " + to_string(mindex_.size()) + "x" + to_string(dim_hyp_) + "\n";
	for (auto& p : mindex_) {
		//VectorIndex vectIndex;
		//for (uint i = 0; i < dim_hyp_; ++i) {
		//	const auto& ind = p.second[i];
		//	vectIndex.add(ind, proofInds_[i]);
		//}
		ret += "\nVAR: " + prover::show(p.first) + "\n";
		ret += "==============================\n";
		for (uint i = 0; i < p.second->vect.size(); ++ i) {
			ret += "index: " + to_string(i) + "\n";
			ret += "\textra inds: " + prover::show(p.second->vect[i]->extraInds()) + "\n";
			ret += "\tall inds: " + prover::show(p.second->vect[i]->allInds()) + "\n";
			ret += "\texprs inds: " + prover::show(p.second->vect[i]->exprsInds()) + "\n";
			ret += p.second->vect[i]->show() + "\n";
			ret += "-----------------------------\n\n";
		}
	}
	return ret;
}

void unify_subs(MatrixIndex& mi, const Prop* pr, MultyUnifiedSubs& ret) {
	MultyUnifiedSubs unif;
	MultyUnifiedSubs gen = mi.compute(unif);
	for (const auto& p : unif) {
		Subst sub = unify_subs(p.second, gen[p.first]);
		if (sub.ok) {
			Subst delta = pr->sub;
			delta.compose(sub);
			ret[p.first] = delta;
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

	cout << "MATRIX no. " << c << ", dim: " << mi.dim_vars() << "x" << mi.dim_hyp() << ", card: " << mi.card_str() << endl;
	if (debug_trie_matrix) {
		cout << "MATRIX no. " << c <<  ", card: " << mi.card_str() << endl ;
		cout << mi.show() << endl;
	}

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

#include "../rus_prover_cartesian.hpp"
#include "rus_prover_index_matrix.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

static void addProofsProp(map<uint, unique_ptr<Vector>>& mindex_, vector<vector<uint>>& proofInds_, uint dim_hyp_, const Hyp::Proofs& proofs, uint i, const ProofsSizeLimit* limit) {
	if (limit) {
		if (limit->descrVect()[i].fixed) {
			throw Error("should not be fixed");
		}
		proofInds_[i] = vector<uint>(limit->descrVect()[i].chosen.size());
		for (uint k = 0; k < limit->descrVect()[i].chosen.size(); ++ k) {
			uint j = limit->descrVect()[i].chosen[k];
			auto p = proofs[j].get();
			for (const auto& x : p->sub) {
				if (!mindex_.count(x.first)) {
					mindex_.emplace(x.first, new Vector(dim_hyp_));
				}
				mindex_.at(x.first)->vect[i]->add(x.second, j);
			}
			proofInds_[i][k] = j;
		}
	} else {
		proofInds_[i] = vector<uint>(proofs.size());
		for (uint j = 0; j < proofs.size(); ++j) {
			auto p = proofs[j].get();
			for (const auto& x : p->sub) {
				if (!mindex_.count(x.first)) {
					mindex_.emplace(x.first, new Vector(dim_hyp_));
				}
				mindex_.at(x.first)->vect[i]->add(x.second, j);
			}
			proofInds_[i][j] = j;
		}
	}
}

static void addProofsHyp(map<uint, unique_ptr<Vector>>& mindex_, vector<vector<uint>>& proofInds_, uint dim_hyp_, const vector<ProofHypIndexed>& hs, uint i, const ProofsSizeLimit* limit) {

	if (limit) {
		if (!limit->descrVect()[i].fixed) {
			throw Error("should be fixed");
		}
		proofInds_[i] = vector<uint>(limit->descrVect()[i].chosen.size());
		for (uint k = 0; k < limit->descrVect()[i].chosen.size(); ++ k) {
			uint j = limit->descrVect()[i].chosen[k];
			ProofHypIndexed hi = hs[j];
			for (const auto& x : hi.proof->sub) {
				if (!mindex_.count(x.first)) {
					mindex_.emplace(x.first, new Vector(dim_hyp_));
				}
				mindex_.at(x.first)->vect[i]->add(x.second, hi.ind);
			}
			proofInds_[i][k] = hi.ind;
		}
	} else {
		proofInds_[i] = vector<uint>(hs.size());
		for (uint j = 0; j < hs.size(); ++j) {
			ProofHypIndexed hi = hs[j];
			for (const auto& x : hi.proof->sub) {
				if (!mindex_.count(x.first)) {
					mindex_.emplace(x.first, new Vector(dim_hyp_));
				}
				mindex_.at(x.first)->vect[i]->add(x.second, hi.ind);
			}
			proofInds_[i][j] = hi.ind;
		}
	}
}

Matrix::Matrix(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs, const ProofsSizeLimit* limit) :
	dim_hyp_(pr->premises.size()), proofInds_(dim_hyp_), empty_(false) {
	for (uint i = 0; i < dim_hyp_; ++ i) {
		const auto& proofs = pr->premises[i]->proofs;
		if (proofs.empty()) {
			empty_ = true;
			break;
		}
		if (pr->premises[i].get() != hy) {
			addProofsProp(mindex_, proofInds_, dim_hyp_, proofs, i, limit);
		} else {
			addProofsHyp(mindex_, proofInds_, dim_hyp_, hs, i, limit);
		}
	}
	for (auto& p : mindex_) {
		for (uint i = 0; i < dim_hyp_; ++i) {
			p.second->vect[i]->init(proofInds_[i]);
		}
	}
}

uint Matrix::card() const {
	uint ret = 1;
	for (const auto& p : proofInds_) {
		ret *= p.size();
	}
	return ret;
}

string Matrix::card_str() const {
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

MultyUnifiedSubs Matrix::compute(MultyUnifiedSubs& unif) {
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
	map<uint, VectorUnifiedUnion> unified_columns;
	Timer timer;
	for (auto& p : mindex_) {
		uint var = p.first;
		Vector* vect = p.second.get();
		try {
			unified_columns[var] = std::move(vect->unify_general());
			if (unified_columns[var].empty()) {
				return MultyUnifiedSubs();
			}
		} catch (Error& err) {
			cout << "while unifying matrix var: " << Lex::toStr(var) << endl;
			throw err;
		}
	}
	add_timer_stats("matrix_unify_time", timer);

	timer.start();
	MultyUnifiedSubs ret = intersect(unified_columns, unif);
	add_timer_stats("matrix_intersect_time", timer);

	return ret;
}

string Matrix::show() const {
	if (empty_) {
		return "empty\n";
	}
	ostringstream oss;
	oss << "DIMENSION: " << dim_hyp_ << "x" << mindex_.size() << endl;
	for (auto& p : mindex_) {
		oss << endl << "VAR: " << Lex::toStr(p.first) << endl;
		oss << p.second->show() << endl;
	}
	return oss.str();
}

}}}}

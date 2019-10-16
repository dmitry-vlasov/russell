#include "rus_prover_unify_matrix.hpp"

#include "../rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

Matrix::Matrix(const vector<vector<SubstInd>>& matr, const ProofsSizeLimit* limit) :
	dim_hyp_(matr.size()), proofInds_(dim_hyp_), empty_(false) {
	for (uint i = 0; i < dim_hyp_; ++ i) {
		const vector<SubstInd>& subs = matr.at(i);
		if (subs.empty()) {
			empty_ = true;
			break;
		}
		proofInds_[i] = vector<uint>(subs.size());
		for (uint j = 0; j < subs.size(); ++j) {
			const SubstInd& s = subs.at(j);
			for (const auto& x : *s.sub) {
				LightSymbol v(x.first, x.second.type);
				if (!mindex_.count(v)) {
					mindex_.emplace(v, new Vector(dim_hyp_));
				}
				mindex_.at(v)->vect[i]->add(x.second.term, s.ind);
			}
			proofInds_[i][j] = s.ind;
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
	map<LightSymbol, VectorUnifiedUnion> unified_columns;
	Timer timer;
	for (auto& p : mindex_) {
		LightSymbol var = p.first;
		Vector* vect = p.second.get();
		try {
			unified_columns[var] = std::move(vect->unify_general());
			if (unified_columns[var].empty()) {
				return MultyUnifiedSubs();
			}
		} catch (Error& err) {
			cout << "while unifying matrix var: " << var << endl;
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
		oss << endl << "VAR: " << p.first << endl;
		oss << p.second->show() << endl;
	}
	return oss.str();
}

}}}}

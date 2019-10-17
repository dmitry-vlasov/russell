#pragma once

#include "../rus_prover_node.hpp"
#include "../rus_prover_limit.hpp"
#include "rus_prover_unify_vector.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

struct Matrix {
	Matrix(const vector<vector<SubstInd>>& subs, const ProofsSizeLimit* limit);

	MultyUnifiedSubs compute(MultyUnifiedSubs& unif);

	string show() const;
	uint card() const;
	string card_str() const;
	uint dim_hyp() const { return dim_hyp_; }
	uint dim_vars() const { return mindex_.size(); }
	bool empty() const { return empty_; }

private:
	uint dim_hyp_;
	map<LightSymbol, unique_ptr<Vector>> mindex_;
	vector<vector<uint>> proofInds_;
	bool empty_;
};

}}}}

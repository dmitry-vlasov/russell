#pragma once

#include "rus_prover_trie_index_vector.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct MatrixIndex {
	MatrixIndex(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs);

	MultyUnifiedSubs compute(MultyUnifiedSubs& unif);

	string show() const;
	uint card() const;
	string card_str() const;
	uint dim_hyp() const { return dim_hyp_; }
	uint dim_vars() const { return mindex_.size(); }
	bool empty() const { return empty_; }

private:
	uint dim_hyp_;
	map<LightSymbol, vector<IndexInt1>> mindex_;
	vector<vector<uint>> proofInds_;
	bool empty_;
};

string show(const MultyUnifiedSubs&);
MultyUnifiedSubs unify_subs_matrix(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs);

extern bool debug_trie_matrix;

}}}}

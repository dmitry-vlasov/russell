#pragma once

#include "rus_prover_trie_vector_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct MatrixUnified {
	MatrixUnified(bool f = true) : full(f) { }
	MatrixUnified intersect(const VectorUnified&) const;
	map<vector<uint>, vector<FlatTermSubst>> unfold() const;

	bool full;
	vector<CartesianCell> vect;
	map<vector<uint>, vector<FlatTermSubst>> unified;
};

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
	map<LightSymbol, VectorIndex> mindex_;
	vector<vector<uint>> proofInds_;
	bool empty_;
};

string show(const MultyUnifiedSubs&);
MultyUnifiedSubs unify_subs_matrix(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs);
MultyUnifiedSubs intersect(const map<LightSymbol, VectorUnified>&, MultyUnifiedSubs& unif);

extern bool debug_trie_matrix;

}}}}

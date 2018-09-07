#include "rus_prover_vector_index.hpp"

namespace mdl { namespace rus { namespace prover {

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
	void addProofs(const Hyp::Proofs& proofs, uint i);
	void addProofs(const vector<ProofHypIndexed>& hs, uint i);
	void addProof(const ProofHyp* p, uint i, uint j);

	uint dim_hyp_;
	map<LightSymbol, vector<IndexInt>> mindex_;
	vector<vector<uint>> proofInds_;
	bool empty_;
};

string show(const MultyUnifiedSubs&);

}}}


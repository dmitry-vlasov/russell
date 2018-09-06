#include "rus_prover_vector_index.hpp"

namespace mdl { namespace rus { namespace prover {

typedef map<vector<uint>, Subst> MultyUnifiedSubs;

struct MatrixIndex {
	MatrixIndex(uint hd) : dim_hyp_(hd), proofInds_(hd) { }

	void addProofs(const Hyp::Proofs& proofs, uint i);
	void addProofs(const vector<ProofHypIndexed>& hs, uint i);
	void addProof(const ProofHyp* p, uint i, uint j);

	MultyUnifiedSubs compute(MultyUnifiedSubs& unif);

	string show() const;
	uint card() const;
	string card_str() const;
	uint dim_hyp() const { return dim_hyp_; }
	uint dim_vars() const { return mindex_.size(); }

private:
	uint dim_hyp_;
	map<LightSymbol, vector<IndexInt>> mindex_;
	vector<vector<uint>> proofInds_;
};

string show(const MultyUnifiedSubs&);

}}}


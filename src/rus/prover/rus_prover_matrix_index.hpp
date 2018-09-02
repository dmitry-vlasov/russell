#include "rus_prover_vector_index.hpp"

namespace mdl { namespace rus { namespace prover {

struct MatrixIndex {
	MatrixIndex(uint hd) : dim_hyp(hd), proofInds_(hd) { }

	void addProofs(const Hyp::Proofs& proofs, uint i);
	void addProof(const ProofHyp* p, uint i, uint j);

	MultyUnifiedSubs compute(MultyUnifiedSubs& unif);

	string show() const;

private:
	uint dim_hyp;
	map<LightSymbol, vector<IndexInt>> mindex_;
	vector<vector<uint>> proofInds_;
};

}}}


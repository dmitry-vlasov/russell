#include "rus_prover_vector_index.hpp"

namespace mdl { namespace rus { namespace prover {

struct MatrixIndex {
	struct Cell {
		IndexInt index;
		uint proofsNumber;
	};

	MatrixIndex(uint hd) : dim_hyp(hd) { }

	void addProofs(const Hyp::Proofs& proofs, uint i);
	void addProof(const ProofHyp* p, uint i, uint j);

	MultyUnifiedSubs compute(MultyUnifiedSubs& unif);

	string show() const;

private:
	uint dim_hyp;
	map<LightSymbol, vector<Cell>> mindex_;
};

}}}


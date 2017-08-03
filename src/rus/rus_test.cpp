#include "prover/rus_prover_tactics.hpp"

namespace mdl { namespace rus {

bool test_proof_with_oracle(Proof* p) {
	prover::Space sp(*p->qeds().begin(), new prover::Oracle(p));
	Proof* reproved = sp.prove();
	bool ret = reproved && reproved->check();
	delete reproved;
	return ret;
}

bool test_with_oracle() {
	for (auto& p : Sys::mod().math.get<Proof>())
		if (!test_proof_with_oracle(p.second.data)) return false;
	return true;
}

}}

#include "prover/rus_prover_tactics.hpp"

namespace mdl { namespace rus {

bool test_proof_with_oracle(Proof* p) {
	cout << "testing proof of " << show_id(p->theorem()->id()) << " ... " << std::flush;
	prover::Space sp(*p->qeds().begin(), new prover::Oracle(p));
	Proof* reproved = sp.prove();
	bool ret = reproved && reproved->check();
	delete reproved;
	cout << (ret ? "success" : "FAIL") << endl;
	return ret;
}

bool test_with_oracle() {
	cout << endl;
	for (auto& p : Sys::mod().math.get<Proof>())
		if (!test_proof_with_oracle(p.second.data)) return false;
	return true;
}

}}

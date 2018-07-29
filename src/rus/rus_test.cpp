#include "prover/rus_prover_tactics.hpp"

namespace mdl { namespace rus {

bool test_proof_with_oracle(Proof* p) {
	cout << "testing proof of " << show_id(p->theorem()->id()) << " ... " << std::flush;
	prover::Space::create(
		*p->qeds().begin(),
		new prover::ProxyTactic(
			new prover::Oracle(p)
			/*prover::show_bits("idx,ch_idx,recurs,ass,expr")*/
		)
	);
	prover::Space::Proved reproved = prover::Space::get()->prove();
	prover::Space::destroy();
	cout << (reproved.size() ? "success" : "FAIL") << endl;
	return reproved.size();
}

bool test_with_oracle() {
	cout << endl;
	for (auto& p : Sys::mod().math.get<Proof>())
		if (!test_proof_with_oracle(p.second.data)) return false;
	return true;
}

}}

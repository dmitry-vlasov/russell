#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>

namespace mdl { namespace rus { namespace {

typedef prover::unify::IndexMap<PropRef> PropIndex;
typedef prover::unify::IndexMap<HypRef> HypIndex;

void reduce_proof_shortcuts(Proof* proof, const PropIndex& propIndex, const HypIndex& hypIndex) {

}

}

#ifdef PARALLEL
#define PARALLEL_REDUCE_PROOF_SHORTCUTS
#endif

void reduce_proof_shortcuts()  {
	vector<Proof*> proofs;
	PropIndex propIndex;
	HypIndex hypIndex;
	for (auto& a : Sys::mod().math.get<Assertion>()) {
		Assertion* ass = a.second.data;
		if (Theorem* thm = dynamic_cast<Theorem*>(ass)) {
			if (Proof* proof = thm->proof.get()) {
				proofs.push_back(proof);
			}
		}
		propIndex.add(
			prover::Tree2Term(*ass->prop->expr.tree(), prover::ReplMode::KEEP_REPL, prover::LightSymbol::ASSERTION_INDEX),
			PropRef(ass)
		);
		for (uint i = 0; i < ass->hyps.size(); ++i) {
			hypIndex.add(
				prover::Tree2Term(*ass->hyps.at(i)->expr.tree(), prover::ReplMode::KEEP_REPL, prover::LightSymbol::ASSERTION_INDEX),
				HypRef(ass, i)
			);
		}
	}
#ifdef PARALLEL_REDUCE_PROOF_SHORTCUTS
	tbb::parallel_for (tbb::blocked_range<size_t>(0, proofs.size()),
		[&proofs, &propIndex, &hypIndex] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				reduce_proof_shortcuts(proofs[i], propIndex, hypIndex);
			}
		}
	);
#else
	for (auto proof : proofs) {
		reduce_proof_shortcuts(proof, propIndex, hypIndex);
	}
#endif
}

}} // mdl::rus


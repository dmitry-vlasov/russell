#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>

namespace mdl { namespace rus { namespace {

typedef prover::unify::IndexMap<PropRef> PropIndex;
typedef prover::unify::IndexMap<HypRef> HypIndex;
typedef prover::unify::IndexMap<Step*> StepIndex;

void reduce_proof_shortcuts(Proof* proof, const PropIndex& propIndex, const HypIndex& hypIndex, const StepIndex& stepIndex) {

}

}

#ifdef PARALLEL
//#define PARALLEL_REDUCE_PROOF_SHORTCUTS
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
				StepIndex stepIndex;
				traverseProof(proofs[i]->qed->step, [&stepIndex](Writable* n) {
					if (Step* step = dynamic_cast<Step*>(n)) {
						stepIndex.add(
							prover::Tree2Term(*step->expr.tree(), prover::ReplMode::DENY_REPL, prover::LightSymbol::MATH_INDEX),
							step
						);
					}
				});
				reduce_proof_shortcuts(proofs[i], propIndex, hypIndex, stepIndex);
			}
		}
	);
#else
	for (auto proof : proofs) {
		StepIndex stepIndex;
		traverseProof(proof->qed->step, [&stepIndex](Writable* n) {
			if (Step* step = dynamic_cast<Step*>(n)) {
				stepIndex.add(
					prover::Tree2Term(*step->expr.tree(), prover::ReplMode::DENY_REPL, prover::LightSymbol::MATH_INDEX),
					step
				);
			}
		});
		reduce_proof_shortcuts(proof, propIndex, hypIndex, stepIndex);
	}
#endif
}

}} // mdl::rus


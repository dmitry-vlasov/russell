#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>
#include <rus/prover/rus_prover_cartesian.hpp>

namespace mdl { namespace rus { namespace {

typedef prover::unify::IndexMap<PropRef> PropIndex;
typedef prover::unify::IndexMap<HypRef> HypIndex;
typedef prover::unify::IndexMap<Step*> StepIndex;

struct Shortcut {
	Shortcut() = default;
	Shortcut(const vector<Writable*>& hs, Step* pr) : hyps(hs), prop(pr) { }
	Shortcut(Shortcut&&) = default;
	vector<Writable*> hyps;
	Step* prop = nullptr;

	string show() const {
		ostringstream oss;
		for (auto h : hyps) {
			oss << *h << endl;
		}
		oss << "------------" << endl;
		oss << *prop << endl;
		return oss.str();
	}
};

struct UnifPair {
	UnifPair(HypIndex::Unified&& u, Writable* n) : unif(std::move(u)), node(n) { }
	HypIndex::Unified unif;
	Writable* node;
};

void reduce_proof_shortcuts(Proof* proof, const PropIndex& propIndex, const HypIndex& hypIndex, const StepIndex& stepIndex) {
	map<Ref, vector<PropIndex::Unified>> props;
	map<Ref, map<const Assertion*, vector<HypIndex::Unified>>> hyps;
	traverseProof(proof->qed->step, [&props, &hyps, &propIndex, &hypIndex](Writable* n) {
		if (Step* step = dynamic_cast<Step*>(n)) {
			prover::Term expr = prover::Tree2Term(
				*step->expr.tree(),
				prover::ReplMode::DENY_REPL,
				prover::LightSymbol::MATH_INDEX
			);
			props.emplace(Ref(step), std::move(propIndex.unify(expr)));
			map<const Assertion*, vector<HypIndex::Unified>> hypsMap;
			for (HypIndex::Unified& unif : hypIndex.unify(expr)) {
				Assertion* ass = unif.data->ass;
				hypsMap[ass].emplace_back(std::move(unif));
			}
			hyps.emplace(Ref(step), std::move(hypsMap));
		} else if (Hyp* hyp = dynamic_cast<Hyp*>(n)) {
			prover::Term expr = prover::Tree2Term(
				*hyp->expr.tree(),
				prover::ReplMode::DENY_REPL,
				prover::LightSymbol::MATH_INDEX
			);
			props.emplace(Ref(hyp), std::move(propIndex.unify(expr)));
			map<const Assertion*, vector<HypIndex::Unified>> hypsMap;
			for (HypIndex::Unified& unif : hypIndex.unify(expr)) {
				Assertion* ass = unif.data->ass;
				hypsMap[ass].emplace_back(std::move(unif));
			}
			hyps.emplace(Ref(hyp), std::move(hypsMap));
		} else {
			throw Error("must be a Step or Hyp");
		}
	});
	map<const Assertion*, Shortcut> shortcuts;
	traverseProof(proof->qed->step, [&props, &hyps, &shortcuts](Writable* n) {
		if (Step* step = dynamic_cast<Step*>(n)) {
			for (PropIndex::Unified& prop_unif : props.at(Ref(step))) {
				vector<vector<UnifPair>> matched_hyps(prop_unif.data->ass->hyps.size());
				traverseProof(step, [&hyps, &matched_hyps, &prop_unif](Writable* m) {
					if (Step* s = dynamic_cast<Step*>(m)) {
						for (HypIndex::Unified& hyp_unif : hyps.at(Ref(s)).at(prop_unif.data->ass)) {
							if (prop_unif.sub.joinable(hyp_unif.sub)) {
								matched_hyps[hyp_unif.data->ind].push_back(UnifPair(std::move(hyp_unif), s));
							}
						}
					} else if (Hyp* h = dynamic_cast<Hyp*>(m)) {
						for (HypIndex::Unified& hyp_unif : hyps.at(Ref(h)).at(prop_unif.data->ass)) {
							if (prop_unif.sub.joinable(hyp_unif.sub)) {
								matched_hyps[hyp_unif.data->ind].push_back(UnifPair(std::move(hyp_unif), h));
							}
						}
					} else {
						throw Error("must be a Step or Hyp");
					}
				});
				prover::CartesianProd<UnifPair> variants;
				for (auto& hyp_vect : matched_hyps) {
					variants.addDim(hyp_vect);
				}
				if (variants.card()) {
					while (true) {
						Assertion* ass = prop_unif.data->ass;
						prover::Subst sub = prop_unif.sub;
						vector<UnifPair> variant = variants.data();
						vector<Writable*> hyps;
						for (UnifPair& up : variant) {
							if (!sub.join(up.unif.sub)) {
								break;
							}
							hyps.push_back(up.node);
						}
						if (sub.ok()) {
							Shortcut shortcut(hyps, step);
							cout << "shortcut found:" << endl;
							cout << shortcut.show() << endl;
							cout << "for assertion: " << Lex::toStr(ass->id()) << endl;
							cout << endl;
							shortcuts.emplace(ass, std::move(shortcut));
						}
						if (!variants.hasNext()) {
							break;
						} else {
							variants.makeNext();
						}
					}
				}
			}
		}
	});
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


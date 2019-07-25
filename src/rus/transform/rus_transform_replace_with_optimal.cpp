#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>
#include <rus/prover/rus_prover_cartesian.hpp>

namespace mdl { namespace rus { namespace {

struct StepRef {
	StepRef(uint i, Substitution&& s) : ind(i), sub(s) { }
	uint ind;
	Substitution sub;
};


void replace_with_optimal(Proof* proof) {
	traverseProof(proof->qed->step, [](Writable* w) {
		if (Step* step = dynamic_cast<Step*>(w)) {
			if (step->ass()->info && step->ass()->info->optimal != step->ass()->id()) {
				const Assertion* optimal = Sys::get().math.get<Assertion>().access(step->ass()->info->optimal);
				Substitution sub = std::move(unify_forth(optimal->prop->expr, step->expr));
				prover::CartesianProd<StepRef> vars;
				for (uint i = 0; i < optimal->hyps.size(); ++ i) {
					vector<StepRef> dimData;
					for (uint j = 0; j < step->refs.size(); ++ j) {
						Substitution s = std::move(unify_forth(optimal->hyps.at(i)->expr, step->refs.at(j)->expr()));
						if (s.join(sub)) {
							dimData.emplace_back(j,std::move(s));
						}
					}
					vars.addDim(dimData);
				}
				if (!vars.card()) {
					throw Error("must not be empty");
				}
				while (true) {
					const vector<StepRef>& var = vars.data();
					Substitution s(sub);
					for (uint i = 0; i < optimal->hyps.size(); ++ i) {
						if (!s.join(var.at(i).sub)) {
							break;
						}
					}
					if (s.ok()) {
						step->set_ass(optimal->id());
						step->refs.clear();
						vector<unique_ptr<Ref>> new_refs;
						for (uint i = 0; i < optimal->hyps.size(); ++ i) {
							int j = var.at(i).ind;
							new_refs.emplace_back(make_unique<Ref>(*step->refs.at(j)));
						}
						step->refs = std::move(new_refs);
						return;
					}
					if (vars.hasNext()) {
						vars.makeNext();
					} else {
						break;
					}
				}
				throw Error("must unify somehow");
			}
		}
	});
}

}

#ifdef PARALLEL
#define PARALLEL_REPLACE_WITH_OPTIMAL_SHORTCUTS
#endif

void replace_with_optimal(const string& opts)  {
	map<string, string> parsed_opts = parse_options(opts);
	uint theorem = parsed_opts.count("theorem") ? Lex::toInt(parsed_opts.at("theorem")) : -1;

	vector<Proof*> proofs;
	for (Assertion& ass : Sys::mod().math.get<Assertion>()) {
		if (Theorem* thm = dynamic_cast<Theorem*>(&ass)) {
			if (Proof* proof = thm->proof.get()) {
				if (theorem == -1 || thm->id() == theorem) {
					proofs.push_back(proof);
				}
			}
		}
	}
#ifdef PARALLEL_REPLACE_WITH_OPTIMAL_SHORTCUTS
	tbb::parallel_for (tbb::blocked_range<size_t>(0, proofs.size()),
		[&proofs] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				replace_with_optimal(proofs[i]);
			}
		}
	);
#else
	for (auto proof : proofs) {
		replace_with_optimal(proof);
	}
#endif
}

}} // mdl::rus


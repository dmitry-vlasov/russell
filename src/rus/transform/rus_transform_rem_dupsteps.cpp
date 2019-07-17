#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>

namespace mdl { namespace rus { namespace {

void reduce_duplcate_steps(Proof* proof) {
	vector<unique_ptr<Step>> new_steps;
	prover::unify::Index expressions;
	map<const Step*, Step*> steps_map;
	for (auto& step : proof->steps) {
		prover::Term term = prover::Tree2Term(*step->expr.tree());
		const vector<uint>* previous = expressions.find(term);
		if (previous && previous->size()) {
			steps_map[step.get()] = new_steps.at(previous->at(0)).get();
		} else {
			uint new_ind = new_steps.size();
			Step* new_step = new Step(
				new_ind, step->kind(), step->ass_id(), step->proof_, step->token
			);
			new_step->expr = std::move(step->expr);
			new_step->sub = std::move(step->sub);
			for (const auto& ref : step->refs) {
				switch (ref->kind()) {
				case Ref::HYP:  new_step->refs.emplace_back(make_unique<Ref>(ref->hyp(), ref->token)); break;
				case Ref::STEP: new_step->refs.emplace_back(make_unique<Ref>(steps_map.at(ref->step()), ref->token)); break;
				}
			}
			expressions.add(term, new_ind);
			steps_map[step.get()] = new_step;
			new_steps.emplace_back(new_step);
		}
	}
	if (new_steps.size() < proof->steps.size()) {
		cout << "proof of theorem " << Lex::toStr(proof->theorem->id()) << " reduced by " << (proof->steps.size() - new_steps.size()) << " steps" << endl;
	}
	proof->steps = std::move(new_steps);
	proof->qed->step = steps_map.at(proof->qed->step);
}

}

#ifdef PARALLEL
#define PARALLEL_DUPLICATE_STEPS
#endif

void reduce_duplcate_steps()  {
	vector<Proof*> proofs;
	for (auto& a : Sys::mod().math.get<Assertion>()) {
		if (Theorem* thm = dynamic_cast<Theorem*>(a.second.data)) {
			if (Proof* proof = thm->proof.get()) {
				proofs.push_back(proof);
			}
		}
	}
#ifdef PARALLEL_DUPLICATE_STEPS
	tbb::parallel_for (tbb::blocked_range<size_t>(0, proofs.size()),
		[&proofs] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				reduce_duplcate_steps(proofs[i]);
			}
		}
	);
#else
	for (auto proof : proofs) {
		reduce_duplcate_steps(proof);
	}
#endif
}

}} // mdl::rus

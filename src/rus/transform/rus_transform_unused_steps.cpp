#include <atomic>
#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>

namespace mdl { namespace rus {

void reduce_unused_steps(Proof* proof, std::atomic<int>& counter) {
	set<const Step*> used_steps;
	traverseProof(proof->qed->step, [&used_steps](Writable* n) {
		if (Step* s = dynamic_cast<Step*>(n)) {
			used_steps.insert(s);
		}
	});
	if (used_steps.size() < proof->steps.size()) {
		//int d = proof->steps.size() - used_steps.size();
		//cout << "proof of theorem " << Lex::toStr(proof->theorem->id()) << " SHOULD BE reduced by " << d << " unused steps" << endl;
		//cout << *proof->theorem << endl;
		map<const Step*, Step*> steps_map;
		vector<unique_ptr<Step>> new_steps;
		for (auto& step : proof->steps) {
			if (used_steps.count(step.get())) {
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
				steps_map[step.get()] = new_step;
				new_steps.emplace_back(new_step);
			}
		}
		int diff = proof->steps.size() - new_steps.size();
		//if (diff != d) {
		//	throw Error("diff != d: " + to_string(diff) + " != " + to_string(d));
		//}
		if (diff > 0) {
			cout << "proof of theorem " << Lex::toStr(proof->theorem->id()) << " reduced by " << diff << " unused steps" << endl;
			counter.store(counter.load() + diff);
		} else {
			throw Error("diff must be > 0");
		}
		proof->steps = std::move(new_steps);
		proof->qed->step = steps_map.at(proof->qed->step);
		//cout << *proof->theorem << endl;
	}
}

#ifdef PARALLEL
//#define PARALLEL_UNUSED_STEPS
#endif

void reduce_unused_steps(const string& opts)  {
	map<string, string> parsed_opts = parse_options(opts);
	uint theorem = parsed_opts.count("theorem") ? Lex::toInt(parsed_opts.at("theorem")) : -1;

	std::atomic<int> counter(0);
	vector<Proof*> proofs;
	for (Assertion& a : Sys::mod().math.get<Assertion>()) {
		if (Theorem* thm = dynamic_cast<Theorem*>(&a)) {
			if (theorem == -1 || thm->id() == theorem) {
				if (Proof* proof = thm->proof.get()) {
					proofs.push_back(proof);
				}
			}
		}
	}
#ifdef PARALLEL_UNUSED_STEPS
	tbb::parallel_for (tbb::blocked_range<size_t>(0, proofs.size()),
		[&proofs, &counter] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				reduce_unused_steps(proofs[i], counter);
			}
		}
	);
#else
	for (auto proof : proofs) {
		reduce_unused_steps(proof, counter);
	}
#endif
	if (counter.load() > 0) {
		cout << "unused steps totally removed: " << counter.load() << endl;
	}
}

}} // mdl::rus

#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>

namespace mdl { namespace rus {

void reduce_unused_steps(Proof* proof, std::atomic<int>& counter);
//void reduce_unused_steps(const string& opts);

void reduce_unused_hyps(Theorem* th, const map<Assertion*, set<Proof*>>& proofs_map, std::atomic<int>& hyp_counter, std::atomic<int>& step_counter) {
	set<Hyp*> used_hyps;
	traverseProof(th->proof->qed->step, [&used_hyps](Writable* n) {
		if (Hyp* h = dynamic_cast<Hyp*>(n)) {
			used_hyps.insert(h);
		}
	});
	uint unused_count = 0;
	vector<bool> hyps_usage(th->hyps.size(), false);
	for (uint i = 0; i < th->hyps.size(); ++ i) {
		Hyp* h = th->hyps.at(i).get();
		if (!used_hyps.count(h)) {
			++ unused_count;
			hyps_usage[i] = false;
		} else {
			hyps_usage[i] = true;
		}
	}
	if (unused_count > 0) {
		th->verify();
		bool AAA = false && (th->id() == Lex::toInt("dvelim"));
		cout << "Theorem " << Lex::toStr(th->id()) << " has " << unused_count << " unused hyps." << endl;
		if (AAA) {
			cout << *th << endl;
			cout << "hyps_usage: {";
			for (bool hu : hyps_usage) {
				cout << (hu ? "T, " : "F, ");
			}
			cout << "}" << endl;
		}
		vector<unique_ptr<Hyp>> reduced_hyps;
		map<Hyp*, Hyp*> old2new;
		map<Hyp*, Hyp*> new2old;
		for (uint i = 0; i < th->hyps.size(); ++ i) {
			Hyp* old_hyp = th->hyps.at(i).get();
			if (hyps_usage.at(i)) {
				Hyp* new_hyp = new Hyp(*old_hyp);
				old2new[old_hyp] = new_hyp;
				new2old[new_hyp] = old_hyp;
				new_hyp->ind = reduced_hyps.size();
				reduced_hyps.emplace_back(new_hyp);
			}
		}
		for (auto& step : th->proof->steps) {
			for (auto& ref : step->refs) {
				if (Hyp* h = ref->hyp()) {
					if (!new2old.count(h)) {
						if (old2new.count(h)) {
							ref.reset(new Ref(old2new.at(h)));
						} else {
							// Unused step
							ref.reset();
						}
					}
				}
			}
		}
		th->hyps = std::move(reduced_hyps);
		complete_assertion_vars(th);
		complete_proof_vars(th->proof.get());
		if (proofs_map.count(th)) {
			for (Proof* p : proofs_map.at(th)) {
				for (auto& s : p->steps) {
					if (s->ass() == th) {
						if (AAA) {
							cout << "in theorem " << Lex::toStr(s->proof()->theorem->id()) << endl;
							cout << "old step: " << *s;
						}
						vector<unique_ptr<Ref>> new_refs;
						for (uint i = 0; i < s->refs.size(); ++ i) {
							auto& ref = s->refs.at(i);
							if (hyps_usage[i]) {
								new_refs.emplace_back(ref.release());
							}
						}
						s->refs = std::move(new_refs);
						if (AAA) {
							cout << "new step: " << *s;
							cout << endl;
						}
					}
				}
				complete_proof_vars(p);
			}
		}
		reduce_unused_steps(th->proof.get(), step_counter);
		th->verify();
		if (AAA) {
			cout << *th << endl;
		}
		hyp_counter.store(hyp_counter.load() + unused_count);
	}
}

#ifdef PARALLEL
//#define PARALLEL_UNUSED_HYPS
#endif

void reduce_unused_hyps(const string& opts)  {
	map<string, string> parsed_opts = parse_options(opts);
	uint theorem = parsed_opts.count("theorem") ? Lex::toInt(parsed_opts.at("theorem")) : -1;

	/*vector<Assertion*> assertions = Sys::mod().math.get<Assertion>().sortedValues(
		[](const Assertion* a1, const Assertion* a2) {
			return a1->token.preceeds(a2->token);
		}
	);*/
	vector<Assertion*> assertions = Sys::mod().math.get<Assertion>().values();
	std::atomic<int> hyp_counter(0);
	std::atomic<int> step_counter(0);
	vector<Theorem*> theorems;
	map<Assertion*, set<Proof*>> proofs_map;
	for (Assertion* a : assertions) {
		if (Theorem* thm = dynamic_cast<Theorem*>(a)) {
			if (thm->proof) {
				if (theorem == -1 || thm->id() == theorem) {
					theorems.push_back(thm);
					for (auto& s : thm->proof->steps) {
						proofs_map[s->ass()].insert(thm->proof.get());
					}
				}
			}
		}
	}
#ifdef PARALLEL_UNUSED_HYPS
	tbb::parallel_for (tbb::blocked_range<size_t>(0, theorems.size()),
		[&theorems, &proofs_map, &counter] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				reduce_unused_hyps(theorems[i], proofs_map, hyp_counter, step_counter);
			}
		}
	);
#else
	for (auto th : theorems) {
		reduce_unused_hyps(th, proofs_map, hyp_counter, step_counter);
	}
#endif
	if (hyp_counter.load() > 0) {
		cout << "unused hypotheses totally removed: " << hyp_counter.load() << endl;
	}
	if (step_counter.load() > 0) {
		cout << "unused steps totally removed: " << step_counter.load() << endl;
	}
}

}} // mdl::rus

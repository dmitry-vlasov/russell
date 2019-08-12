#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>

namespace mdl { namespace rus {

void reduce_unused_steps(Proof* proof, std::atomic<int>& counter);

struct HypsInfo {
	HypsInfo() = default;
	HypsInfo(uint a) : hyps_usage(a, false) { }
	HypsInfo(const HypsInfo&) = default;
	HypsInfo(HypsInfo&&) = default;
	HypsInfo& operator = (const HypsInfo&) = default;
	uint unused_count = 0;
	vector<bool> hyps_usage;
};

typedef cmap<Assertion*, HypsInfo> HypsInfoMap;

HypsInfo find_unused_hyps(Theorem* th, std::atomic<int>& hyp_counter, std::atomic<int>& step_counter) {
	set<Hyp*> used_hyps;
	traverseProof(th->proof->qed->step, [&used_hyps](Writable* n) {
		if (Hyp* h = dynamic_cast<Hyp*>(n)) {
			used_hyps.insert(h);
		}
	});
	HypsInfo info(th->hyps.size());
	for (uint i = 0; i < th->hyps.size(); ++ i) {
		Hyp* h = th->hyps.at(i).get();
		if (!used_hyps.count(h)) {
			++ info.unused_count;
			info.hyps_usage[i] = false;
		} else {
			info.hyps_usage[i] = true;
		}
	}
	if (info.unused_count > 0) {
		cout << "Theorem " << Lex::toStr(th->id()) << " has " << info.unused_count << " unused hyps." << endl;
		vector<unique_ptr<Hyp>> reduced_hyps;
		map<Hyp*, Hyp*> old2new;
		map<Hyp*, Hyp*> new2old;
		for (uint i = 0; i < th->hyps.size(); ++ i) {
			Hyp* old_hyp = th->hyps.at(i).get();
			if (info.hyps_usage.at(i)) {
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
		hyp_counter.store(hyp_counter.load() + info.unused_count);
		reduce_unused_steps(th->proof.get(), step_counter);
	}
	return info;
}

void reduce_unused_hyps(Theorem* th, const HypsInfoMap& info_map, std::atomic<int>& step_counter) {
	bool was_changed = false;
	for (auto& s : th->proof->steps) {
		HypsInfoMap::const_accessor a;
		if (info_map.find(a, s->ass())) {
			HypsInfo info = a->second;
			vector<unique_ptr<Ref>> new_refs;
			for (uint i = 0; i < s->refs.size(); ++ i) {
				auto& ref = s->refs.at(i);
				if (info.hyps_usage[i]) {
					new_refs.emplace_back(ref.release());
				}
			}
			s->refs = std::move(new_refs);
			was_changed = true;
		}
	}
	if (was_changed) {
		complete_proof_vars(th->proof.get());
		reduce_unused_steps(th->proof.get(), step_counter);
	}
	//th->verify();
}

#ifdef PARALLEL
#define PARALLEL_UNUSED_HYPS
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
	for (Assertion* a : assertions) {
		if (Theorem* thm = dynamic_cast<Theorem*>(a)) {
			if (thm->proof) {
				if (theorem == -1 || thm->id() == theorem) {
					theorems.push_back(thm);
				}
			}
		}
	}
	HypsInfoMap hyps_info_map;
#ifdef PARALLEL_UNUSED_HYPS
	tbb::parallel_for (tbb::blocked_range<size_t>(0, theorems.size()),
		[&theorems, &hyp_counter, &step_counter, &hyps_info_map] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				HypsInfo info = find_unused_hyps(theorems[i], hyp_counter, step_counter);
				if (info.unused_count > 0) {
					HypsInfoMap::accessor a;
					hyps_info_map.insert(a, theorems[i]);
					a->second = info;
				}
			}
		}
	);
	tbb::parallel_for (tbb::blocked_range<size_t>(0, theorems.size()),
		[&theorems, &hyps_info_map, &step_counter] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				reduce_unused_hyps(theorems[i], hyps_info_map, step_counter);
			}
		}
	);
#else
	for (auto thm : theorems) {
		HypsInfo info = find_unused_hyps(thm, hyp_counter, step_counter);
		if (info.unused_count > 0) {
			HypsInfoMap::accessor a;
			hyps_info_map.insert(a, thm);
			a->second = info;
		}
	}
	for (auto thm : theorems) {
		reduce_unused_hyps(thm, hyps_info_map, step_counter);
	}
#endif
	verify();
	if (hyp_counter.load() > 0) {
		cout << "unused hypotheses totally removed: " << hyp_counter.load() << endl;
	}
	if (step_counter.load() > 0) {
		cout << "unused steps totally removed: " << step_counter.load() << endl;
	}
}

}} // mdl::rus

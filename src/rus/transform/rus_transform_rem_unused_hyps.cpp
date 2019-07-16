#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>

namespace mdl { namespace rus { namespace {

void reduce_unused_hyps(Theorem* th, const map<Assertion*, vector<Step*>>& steps_map) {
	set<Hyp*> used_hyps;
	traverseProof(th->proof->qed->step, [&used_hyps](Writable* n) {
		if (Hyp* h = dynamic_cast<Hyp*>(n)) {
			used_hyps.insert(h);
		}
	});
	uint unused_count = 0;
	vector<bool> hyps_usage;
	for (uint i = 0; i < th->hyps.size(); ++ i) {
		auto& h = th->hyps.at(i);
		if (!used_hyps.count(h.get())) {
			++ unused_count;
			hyps_usage[i] = false;
		} else {
			hyps_usage[i] = true;
		}
	}
	if (unused_count > 0) {
		cout << "Theorem " << Lex::toStr(th->id()) << " has " << unused_count << " unused hyps." << endl;
		vector<unique_ptr<Hyp>> reduced_hyps;
		map<Hyp*, Hyp*> old2new;
		for (uint i = 0; i < th->hyps.size(); ++ i) {
			auto& h = th->hyps.at(i);
			if (hyps_usage.at(i)) {
				reduced_hyps.emplace_back(make_unique<Hyp>(*h));
				old2new[h.get()] = reduced_hyps.back().get();
			}
		}
		th->hyps = std::move(reduced_hyps);
		traverseProof(th->proof->qed->step, [&old2new](Writable* n) {
			if (Step* s = dynamic_cast<Step*>(n)) {
				for (auto& ref : s->refs) {
					if (Hyp* oldHyp = ref->hyp()) {
						ref.reset(new Ref(old2new.at(oldHyp)));
					}
				}
			}
		});
		for (Step* s : steps_map.at(th)) {
			vector<unique_ptr<Ref>> new_refs;
			for (uint i = 0; i < s->refs.size(); ++ i) {
				auto& ref = s->refs.at(i);
				if (hyps_usage[i]) {
					new_refs.emplace_back(ref.release());
				}
			}
			s->refs = std::move(new_refs);
		}
	}
}

}

#ifdef PARALLEL
#define PARALLEL_UNUSED_HYPS
#endif

void reduce_unused_hyps()  {
	vector<Theorem*> theorems;
	map<Assertion*, vector<Step*>> steps_map;
	for (auto& a : Sys::mod().math.get<Assertion>()) {
		if (Theorem* th = dynamic_cast<Theorem*>(a.second.data)) {
			if (th->proof) {
				theorems.push_back(th);
				traverseProof(th->proof->qed->step, [&steps_map](Writable* n) {
					if (Step* s = dynamic_cast<Step*>(n)) {
						steps_map[s->ass()].push_back(s);
					}
				});
			}
		}
	}
#ifdef PARALLEL_UNUSED_HYPS
	tbb::parallel_for (tbb::blocked_range<size_t>(0, theorems.size()),
		[&theorems, &steps_map] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				reduce_unused_hyps(theorems[i], steps_map);
			}
		}
	);
#else
	for (auto th : theorems) {
		reduce_unused_hyps(th, steps_map);
	}
#endif
}

}} // mdl::rus

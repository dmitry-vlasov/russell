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
		cout << "Theorem " << Lex::toStr(th->id()) << " has " << unused_count << " unused hyps." << endl;
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
		traverseProof(th->proof->qed->step, [&old2new, &new2old](Writable* n) {
			if (Step* s = dynamic_cast<Step*>(n)) {
				for (auto& ref : s->refs) {
					if (Hyp* h = ref->hyp()) {
						if (!new2old.count(h)) {
							ref.reset(new Ref(old2new.at(h)));
						}
					}
				}
			}
		});
		th->hyps = std::move(reduced_hyps);
		if (steps_map.count(th)) {
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

}

#ifdef PARALLEL
//#define PARALLEL_UNUSED_HYPS
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

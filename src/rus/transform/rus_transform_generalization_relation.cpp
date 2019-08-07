#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>
#include <rus/prover/rus_prover_maker.hpp>
#include <rus/prover/rus_prover_ass.hpp>
#include <rus/prover/rus_prover_cartesian.hpp>

namespace mdl { namespace rus {

using namespace prover;

namespace {

typedef prover::unify::IndexMap<PropRef> PropIndex;
typedef prover::unify::IndexMap<HypRef> HypIndex;

unique_ptr<Theorem> make_gen_rel_theorem(const GenRel& rel, uint th_name) {
	unique_ptr<Theorem> ret = make_unique<Theorem>(th_name);
	const Assertion* less = Sys::get().math.get<Assertion>().access(rel.less);
	for (auto& h : less->hyps) {
		ret->hyps.emplace_back(make_unique<rus::Hyp>(*h));
	}
	ret->prop = make_unique<rus::Prop>(*less->prop);
	ret->proof = make_unique<Proof>();
	Step* step = new Step(0, Step::ASS, rel.more, ret->proof.get());
	for (uint i = 0; i < rel.hyps.size(); ++ i) {
		uint j = rel.hyps.at(i);
		step->refs.emplace_back(new rus::Ref(ret->hyps.at(j).get()));
	}
	step->expr = ret->prop->expr;
	ret->proof->steps.emplace_back(step);
	ret->proof->qed = make_unique<Qed>(ret->prop.get(), step);
	return ret;
}

void process_gen_rel(const GenRel& rel) {
	uint th_name = Lex::toInt(Lex::toStr(rel.less) + "_less_gen_then_" + Lex::toStr(rel.more));
	if (Sys::get().math.get<Assertion>().has(th_name)) {
		// check
		Assertion* ass = Sys::mod().math.get<Assertion>().access(th_name);
		if (Theorem* thm = dynamic_cast<Theorem*>(ass)) {
			thm->verify();
		} else {
			throw Error("must be a theorem");
		}
	} else {
		unique_ptr<Theorem> gen_thm = make_gen_rel_theorem(rel, th_name);
		try {
			gen_thm->verify();
		} catch (Error& err) {
			err.msg += "testing gen relation: " + Lex::toStr(th_name) + "\n";
			err.msg += gen_thm->show() + "\n";
			throw err;
		}
	}
}

void generaliziation_relation(Assertion* as, const PropIndex& propIndex, const HypIndex& hypIndex, std::atomic<int>& counter) {
	Ass a0(*as, true);
	VarRepl renaming = specialFreshVars(a0.vars());
	Ass a = a0.apply(renaming);

	map<const Assertion*, vector<vector<HypIndex::Unified>>> hyps_map;
	for (uint i = 0; i < a.hyps.size(); ++ i) {
		const Term& h = a.hyps.at(i);
		for (const HypIndex::Unified& unif : hypIndex.unify(h)) {
			if (!hyps_map.count(unif.data->ass)) {
				hyps_map.emplace(unif.data->ass, vector<vector<HypIndex::Unified>>(a.hyps.size()));
			}
			hyps_map.at(unif.data->ass).at(i).emplace_back(unif);
		}
	}
	struct HypsUnified {
		HypsUnified(vector<uint>&& i, Subst&& s) : inds(std::move(i)), sub(std::move(s)) { }
		vector<uint> inds;
		Subst sub;
	};
	map<const Assertion*, vector<HypsUnified>> less_general;
	for (const PropIndex::Unified& prop_unif : propIndex.unify(a.prop)) {
		const Assertion* ass = prop_unif.data->ass;
		if (ass == as || !hyps_map.count(ass)) {
			continue;
		}
		CartesianProd<HypIndex::Unified> variants;
		for (auto& v : hyps_map.at(ass)) {
			variants.addDim(v);
		}
		if (!variants.card()) {
			continue;
		} else {
			Watchdog watchdog(1000, "check generalizations of assertion " + Lex::toStr(as->id()));
			try {
				while (true) {
					watchdog.check();
					const vector<HypIndex::Unified>& var = variants.data();
					vector<uint> inds;
					Subst s = prop_unif.sub;
					for (const HypIndex::Unified& hyp_unif : var) {
						inds.push_back(hyp_unif.data->ind);
						if (!s.compose(hyp_unif.sub)) {
							break;
						}
					}
					renaming.inverse().apply(s);
					if (s.ok() && as->disj.satisfies(Subst2Substitution(s), &ass->disj)) {
						less_general[ass].emplace_back(HypsUnified(std::move(inds), std::move(s)));
					}
					if (variants.hasNext()) {
						variants.makeNext();
					} else {
						break;
					}
				}
			} catch (Timeout& timeout) {
				cout << timeout.what() << endl;
			}
		}
	}
	if (less_general.size()) {
		vector<GenRel> less_general_rel;
		vector<GenRel> equal_general_rel;
		for (auto& p : less_general) {
			const Assertion* ass = p.first;
			if (!p.second.size()) {
				throw Error("less general subs vector must be non-empty");
			}
			if (match(*ass, *as).size()) {
				equal_general_rel.emplace_back(ass->id(), as->id(), true, p.second.front().inds);
				process_gen_rel(equal_general_rel.back());
			} else {
				less_general_rel.emplace_back(ass->id(), as->id(), false, p.second.front().inds);
				process_gen_rel(less_general_rel.back());
			}
			for (const auto& s : p.second) {
				Ass a0(*as, true);
				Ass a1(*ass, false);
				if (a0.apply(s.sub) != a1) {
					string err;
					err += "wrong matching:\n";
					err += "a:\n" + a0.show() + "\n";
					err += "a1:\n" + a1.show() + "\n";
					err += "sub:\n" + s.sub.show() + "\n";
					throw Error(err);
				}
			}
		}
		if (!as->info) {
			as->info = make_unique<Assertion::Info>();
		}
		as->info->lessGeneral = std::move(less_general_rel);
		as->info->equalGeneral = std::move(equal_general_rel);
		counter.store(counter.load() + 1);
	}
}

}

#ifdef PARALLEL
//#define PARALLEL_GENERALIZATION_RELATION
#endif

void show_generalization_info(const vector<Assertion*>& assertions) {
	for (auto a : assertions) {
		if (a->info && (a->info->lessGeneral.size() || a->info->moreGeneral.size() || a->info->equalGeneral.size())) {
			cout << "For assertion " << Lex::toStr(a->id()) << " ";
			cout << "optimal is: " << Lex::toStr(a->info->isOptimal ? a->id() : a->info->optimal.more) << ", ";
			cout << "those are ";
			if (a->info->lessGeneral.size()) {
				cout << "less general: {";
				for (auto& l : a->info->lessGeneral) {
					cout << Lex::toStr(l.less) << ", ";
				}
				cout << "} ";
			}
			if (a->info->equalGeneral.size()) {
				cout << "equal general: {";
				for (auto& e : a->info->equalGeneral) {
					cout << Lex::toStr(e.less) << ", ";
				}
				cout << "} ";
			}
			if (a->info->moreGeneral.size()) {
				cout << "more general: {";
				for (auto& m : a->info->moreGeneral) {
					cout << Lex::toStr(m.more) << ", ";
				}
				cout << "}";
			}
			cout << endl;
		}
	}
}

void decide_an_optimal(Assertion* a) {
	if (!a->info) {
		throw Error("info must be defined");
	}
	if (a->info->optimalIsDefined()) {
		return;
	}
	if (!a->info->moreGeneral.size()) {
		if (!a->info->equalGeneral.size()) {
			a->info->isOptimal = true;
		} else {
			std::sort(
				a->info->equalGeneral.begin(),
				a->info->equalGeneral.end(),
				[](const GenRel& l, const GenRel& g) {
					return Lex::toStr(l.more).size() < Lex::toStr(g.more).size();
				}
			);
			GenRel optimal;
			Assertion* optimal_a = nullptr;
			for (GenRel& e : a->info->equalGeneral) {
				Assertion* eq_a = Sys::mod().math.get<Assertion>().access(e.more);
				if (!optimal.isDefined()) {
					optimal = e;
					optimal_a = eq_a;
				}
				if (Theorem* th = dynamic_cast<Theorem*>(eq_a)) {
					optimal = e;
					optimal_a = th;
					break;
				}
			}
			a->info->optimal = optimal;
			optimal_a->info->isOptimal = true;

			optimal_a->info->isOptimal = true;
			for (GenRel& e : a->info->equalGeneral) {
				Assertion* eq_a = Sys::mod().math.get<Assertion>().access(e.more);
				auto it = std::find_if(
					eq_a->info->equalGeneral.begin(),
					eq_a->info->equalGeneral.end(),
					[optimal](const GenRel& r) { return r.more == optimal.more; }
				);
				if (it == eq_a->info->equalGeneral.end()) {
					throw Error("optimal is not found");
				}
				eq_a->info->optimal = *it;
			}
		}
	} else {
		for (auto& m : a->info->moreGeneral) {
			decide_an_optimal(Sys::mod().math.get<Assertion>().access(m.more));
		}
		Assertion* more_a = Sys::mod().math.get<Assertion>().access(a->info->moreGeneral.front().more);
		a->info->optimal =
			more_a->info->isOptimal ?
			a->info->moreGeneral.front() :
			more_a->info->optimal;
		Assertion* optimal_a = Sys::mod().math.get<Assertion>().access(a->info->optimal.more);
		if (!optimal_a->info->isOptimal) {
			throw Error("must be optimal");
		}
	}
}

void generaliziation_relation(const string& opts)  {
	map<string, string> parsed_opts = parse_options(opts);
	uint theorem = parsed_opts.count("theorem") ? Lex::toInt(parsed_opts.at("theorem")) : -1;

	std::atomic<int> counter(0);
	vector<Assertion*> assertions;
	PropIndex propIndex;
	HypIndex hypIndex;
	for (Assertion& ass : Sys::mod().math.get<Assertion>()) {
		assertions.push_back(&ass);
		propIndex.add(
			prover::Tree2Term(*ass.prop->expr.tree(), false),
			PropRef(&ass)
		);
		for (uint i = 0; i < ass.hyps.size(); ++i) {
			hypIndex.add(
				prover::Tree2Term(*ass.hyps.at(i)->expr.tree(), false),
				HypRef(&ass, i)
			);
		}
	}
	propIndex.init();
	hypIndex.init();
#ifdef PARALLEL_GENERALIZATION_RELATION
	tbb::parallel_for (tbb::blocked_range<size_t>(0, assertions.size()),
		[&assertions, &counter, &propIndex, &hypIndex] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				generaliziation_relation(assertions[i], propIndex, hypIndex, counter);
			}
		}
	);
#else
	for (auto a : assertions) {
		generaliziation_relation(a, propIndex, hypIndex, counter);
	}
#endif

	for (auto a : assertions) {
		if (a->info && a->info->lessGeneral.size()) {
			for (GenRel l : a->info->lessGeneral) {
				Assertion* less = Sys::mod().math.get<Assertion>().access(l.less);
				if (!less->info) {
					less->info = make_unique<Assertion::Info>();
				}
				less->info->moreGeneral.emplace_back(l);
			}
		}
	}
	for (auto a : assertions) {
		if (a->info) {
			decide_an_optimal(a);
		}
	}
	show_generalization_info(assertions);
	if (counter.load() > 0) {
		cout << "total number of generalizations: " << counter.load() << endl;
	}
}

}} // mdl::rus

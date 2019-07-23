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

void generaliziation_relation(Assertion* as, const PropIndex& propIndex, const HypIndex& hypIndex, std::atomic<int>& counter) {
	Ass a = Ass(*as, ReplMode::KEEP_REPL).specialFreshVars();

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
	map<const Assertion*, vector<Subst>> less_general;
	for (const PropIndex::Unified& unif : propIndex.unify(a.prop)) {
		const Assertion* ass = unif.data->ass;
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
					Subst s = unif.sub;
					for (const HypIndex::Unified& unif : var) {
						if (!s.compose(unif.sub)) {
							break;
						}
					}
					if (s.ok()) {
						less_general[ass].emplace_back(std::move(s));
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
		vector<uint> less_general_ids;
		vector<uint> equal_general_ids;
		for (auto& p : less_general) {
			const Assertion* ass = p.first;
			if (match(*ass, *as).size()) {
				equal_general_ids.push_back(ass->id());
			} else {
				less_general_ids.push_back(ass->id());
			}
			for (const auto& s : p.second) {
				Ass a1(*ass, ReplMode::DENY_REPL);
				if (a.apply(s) != a1) {
					string err;
					err += "wrong matching:\n";
					err += "a:\n" + a.show() + "\n";
					err += "a1:\n" + a1.show() + "\n";
					err += "sub:\n" + s.show() + "\n";
					throw Error(err);
				}
			}
		}
		if (!as->info) {
			as->info = make_unique<Assertion::Info>();
		}
		as->info->lessGeneral = std::move(less_general_ids);
		as->info->equalGeneral = std::move(equal_general_ids);
		counter.store(counter.load() + 1);
	}
}

}

#ifdef PARALLEL
#define PARALLEL_GENERALIZATION_RELATION
#endif

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
			prover::Tree2Term(*ass.prop->expr.tree(), prover::ReplMode::DENY_REPL, prover::LightSymbol::MATH_INDEX),
			PropRef(&ass)
		);
		for (uint i = 0; i < ass.hyps.size(); ++i) {
			hypIndex.add(
				prover::Tree2Term(*ass.hyps.at(i)->expr.tree(), prover::ReplMode::DENY_REPL, prover::LightSymbol::MATH_INDEX),
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
			for (uint id : a->info->lessGeneral) {
				Assertion* less = Sys::mod().math.get<Assertion>().access(id);
				if (!less->info) {
					less->info = make_unique<Assertion::Info>();
				}
				less->info->moreGeneral.push_back(a->id());
			}
		}
	}
	for (auto a : assertions) {
		if (a->info && (a->info->lessGeneral.size() || a->info->moreGeneral.size() || a->info->equalGeneral.size())) {
			cout << "For assertion " << Lex::toStr(a->id()) << " those are ";
			if (a->info->lessGeneral.size()) {
				cout << "less general: {";
				for (auto l : a->info->lessGeneral) {
					cout << Lex::toStr(l) << ", ";
				}
				cout << "} ";
			}
			if (a->info->equalGeneral.size()) {
				cout << "equal general: {";
				for (auto l : a->info->equalGeneral) {
					cout << Lex::toStr(l) << ", ";
				}
				cout << "} ";
			}
			if (a->info->moreGeneral.size()) {
				cout << "more general: {";
				for (auto l : a->info->moreGeneral) {
					cout << Lex::toStr(l) << ", ";
				}
				cout << "}";
			}
			cout << endl;
		}
	}
	if (counter.load() > 0) {
		cout << "total number of generalizations: " << counter.load() << endl;
	}
}

}} // mdl::rus

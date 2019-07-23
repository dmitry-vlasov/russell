#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>
#include <rus/prover/rus_prover_maker.hpp>

namespace mdl { namespace rus { namespace {

typedef prover::unify::IndexMap<PropRef> PropIndex;
typedef prover::unify::IndexMap<HypRef> HypIndex;

void generaliziation_relation(Assertion* thm, const PropIndex& propIndex, const HypIndex& hypIndex, std::atomic<int>& counter) {

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
	if (counter.load() > 0) {
		cout << "totally generalization pairs: " << counter.load() << endl;
	}
}

}} // mdl::rus

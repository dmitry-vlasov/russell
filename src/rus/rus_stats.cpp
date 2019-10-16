#include <rus_ast.hpp>

namespace mdl { namespace rus {

const string subproof_prefix = "subproof_";
const string generalize_prefix = "gen_";

extern int generalization_works_count;

struct TheoremStats {
	uint num_theorems    = 0;
	uint num_hyps        = 0;
	uint num_outer_vars  = 0;
	uint num_inner_vars  = 0;
	uint num_outer_disj  = 0;
	uint num_inner_disj  = 0;
	uint num_steps       = 0;

	string report_stats(const string& opts) const {
		ostringstream oss;
		oss << "\tnum theorems:    " << num_theorems << endl;
		oss << "\tnum hyps:        " << num_hyps << endl;
		oss << "\tnum outer vars:  " << num_outer_vars << endl;
		oss << "\tnum inner vars:  " << num_inner_vars << endl;
		oss << "\tnum outer disj:  " << num_outer_disj << endl;
		oss << "\tnum inner disj:  " << num_inner_disj << endl;
		oss << "\tnum steps:       " << num_steps << endl;
		return oss.str();
	}
};

struct Stats {
	uint num_sources     = 0;
	uint num_consts      = 0;
	uint num_types       = 0;
	uint num_rules       = 0;
	uint num_assertions  = 0;
	uint num_axioms      = 0;
	uint num_defs        = 0;
	uint num_theorems    = 0;
	map<string, TheoremStats> theorem_stats;

	set<uint> all_assertions;
	set<uint> replaceable_assertions;
	set<uint> used_assertions;
	set<uint> unused_assertions;
	set<uint> unused_replaceable_assertions;

	string report_stats(const string& opts) const {
		ostringstream oss;
		oss << "num sources:     " << num_sources << endl;
		oss << "num consts:      " << num_consts << endl;
		oss << "num types:       " << num_types << endl;
		oss << "num rules:       " << num_rules << endl;
		oss << "num assertions:  " << num_assertions << endl;
		oss << "num axioms:      " << num_axioms << endl;
		oss << "num defs:        " << num_defs << endl;

		for (const auto& p : theorem_stats) {
			oss << "theorem kind: " << p.first << endl;
			oss << p.second.report_stats(opts);
			oss << endl;
		}

		oss << "num repl. ass.   " << replaceable_assertions.size() << endl;
		oss << "num used ass.    " << used_assertions.size() << endl;
		oss << "num unused ass.  " << unused_assertions.size() << endl;
		oss << "num repl.unused: " << unused_replaceable_assertions.size() << endl;
		oss << endl;
		oss << "generalization_works_count: " << generalization_works_count << endl;
		return oss.str();
	}
};

Stats produce_stats(const string& opts) {
	map<string, string> parsed_opts = parse_options(opts);
	Stats stats;
	stats.num_sources    = Sys::get().math.get<Source>().size();
	stats.num_consts     = Sys::get().math.get<Constant>().size();
	stats.num_types      = Sys::get().math.get<Type>().size();
	stats.num_rules      = Sys::get().math.get<Rule>().size();
	stats.num_assertions = Sys::get().math.get<Assertion>().size();

	auto account_theorem = [&stats](const Theorem* th, const string& kind) {
		stats.theorem_stats[kind].num_theorems += 1;
		stats.theorem_stats[kind].num_steps += th->proof->steps.size();
		stats.theorem_stats[kind].num_inner_vars += th->proof->vars.v.size();
		stats.theorem_stats[kind].num_inner_disj += th->proof->disj.dvars.size();
		stats.theorem_stats[kind].num_hyps += th->hyps.size();
		stats.theorem_stats[kind].num_outer_vars += th->vars.v.size();
		stats.theorem_stats[kind].num_outer_disj += th->disj.dvars.size();
	};

	for (const Assertion& a : Sys::get().math.get<Assertion>()) {
		stats.all_assertions.insert(a.id());
		if (a.info && !a.info->isOptimal) {
			stats.replaceable_assertions.insert(a.id());
		}
		if (dynamic_cast<const Axiom*>(&a)) {
			stats.num_axioms += 1;
		} else if (dynamic_cast<const Def*>(&a)) {
			stats.num_defs += 1;
		} else if (const Theorem* th = dynamic_cast<const Theorem*>(&a)) {
			stats.num_theorems += 1;
			string name = Lex::toStr(th->id());
			if (string_starts_with(name, subproof_prefix)) {
				account_theorem(th, subproof_prefix);
			} else if (string_starts_with(name, generalize_prefix)) {
				account_theorem(th, generalize_prefix);
			} else {
				account_theorem(th, "original");
			}
			account_theorem(th, "all");
			for (auto& s : th->proof->steps) {
				stats.used_assertions.insert(s->ass()->id());
			}
		}
	}
	for (uint id : stats.all_assertions) {
		if (!stats.used_assertions.count(id)) {
			stats.unused_assertions.insert(id);
			if (stats.replaceable_assertions.count(id)) {
				stats.unused_replaceable_assertions.insert(id);
			}
		}
	}
	return stats;
}

string report_stats(const string& opts) {
	map<string, string> parsed_opts = parse_options(opts);
	string ret = produce_stats(opts).report_stats(opts);
	cout << ret;
	return ret;
}

}} // mdl::rus

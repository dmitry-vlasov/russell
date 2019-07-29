#include <rus_ast.hpp>

namespace mdl { namespace rus {

struct Stats {
	uint num_sources    = 0;
	uint num_consts     = 0;
	uint num_types      = 0;
	uint num_rules      = 0;
	uint num_assertions = 0;
	uint num_hyps       = 0;
	uint num_outer_vars = 0;
	uint num_inner_vars = 0;
	uint num_outer_disj = 0;
	uint num_inner_disj = 0;
	uint num_axioms     = 0;
	uint num_defs       = 0;
	uint num_theorems   = 0;
	uint num_steps      = 0;

	set<uint> all_assertions;
	set<uint> replaceable_assertions;
	set<uint> used_assertions;
	set<uint> unused_assertions;
	set<uint> unused_replaceable_assertions;
};

Stats produce_stats(const string& opts) {
	map<string, string> parsed_opts = parse_options(opts);
	Stats stats;
	stats.num_sources    = Sys::get().math.get<Source>().size();
	stats.num_consts     = Sys::get().math.get<Constant>().size();
	stats.num_types      = Sys::get().math.get<Type>().size();
	stats.num_rules      = Sys::get().math.get<Rule>().size();
	stats.num_assertions = Sys::get().math.get<Assertion>().size();
	for (const Assertion& a : Sys::get().math.get<Assertion>()) {
		stats.all_assertions.insert(a.id());
		if (a.info && a.info->optimal != a.id()) {
			stats.replaceable_assertions.insert(a.id());
		}
		stats.num_hyps += a.hyps.size();
		stats.num_outer_vars += a.vars.v.size();
		stats.num_outer_disj += a.disj.dvars.size();
		if (dynamic_cast<const Axiom*>(&a)) {
			stats.num_axioms += 1;
		} else if (dynamic_cast<const Def*>(&a)) {
			stats.num_defs += 1;
		} else if (const Theorem* th = dynamic_cast<const Theorem*>(&a)) {
			stats.num_theorems += 1;
			stats.num_steps += th->proof->steps.size();
			stats.num_inner_vars += th->proof->vars.v.size();
			stats.num_inner_disj += th->proof->disj.dvars.size();
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

string report_stats(const Stats& stats, const string& opts) {
	ostringstream oss;
	oss << "num sources:     " << stats.num_sources << endl;
	oss << "num consts:      " << stats.num_consts << endl;
	oss << "num types:       " << stats.num_types << endl;
	oss << "num rules:       " << stats.num_rules << endl;
	oss << "num assertions:  " << stats.num_assertions << endl;
	oss << "num hyps:        " << stats.num_hyps << endl;
	oss << "num outer vars:  " << stats.num_outer_vars << endl;
	oss << "num inner vars:  " << stats.num_inner_vars << endl;
	oss << "num outer disj:  " << stats.num_outer_disj << endl;
	oss << "num inner disj:  " << stats.num_inner_disj << endl;
	oss << "num axioms:      " << stats.num_axioms << endl;
	oss << "num defs:        " << stats.num_defs<< endl;
	oss << "num theorems:    " << stats.num_theorems << endl;
	oss << "num steps:       " << stats.num_steps << endl;
	oss << "num repl. ass.   " << stats.replaceable_assertions.size() << endl;
	oss << "num used ass.    " << stats.used_assertions.size() << endl;
	oss << "num unused ass.  " << stats.unused_assertions.size() << endl;
	oss << "num repl.unused: " << stats.unused_replaceable_assertions.size() << endl;
	return oss.str();
}

string report_stats(const string& opts) {
	map<string, string> parsed_opts = parse_options(opts);
	string ret = report_stats(produce_stats(opts), opts);
	cout << ret;
	return ret;
}

}} // mdl::rus

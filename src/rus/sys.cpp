#include "rus/sys.hpp"

namespace mdl { namespace rus { namespace {

bool parse_rus(System& rus) {
	try {
		if (rus.config.verbose) cout << "parsing russell source ... " << flush;
		rus.timers["read"].start();
		uint lab = Lex::toInt(rus.config.in);
		Source* src = parse(rus.config.in);
		rus.math.sources[lab] = src;
		rus.timers["read"].stop();
		if (rus.config.verbose) cout << "done in " << rus.timers["read"] << endl;
		return true;
	} catch (Error& err) {
		rus.error += '\n';
		rus.error += err.what();
		return false;
	}
}

bool parse_exp(System& rus) {
	try {
		if (rus.config.verbose) cout << "parsing expressions ... " << flush;
		rus.timers["expr"].start();
		expr::parse();
		rus.timers["expr"].stop();
		if (rus.config.verbose) cout << "done in " << rus.timers["expr"] << endl;
		return true;
	} catch (Error& err) {
		rus.error += '\n';
		rus.error += err.what();
		return false;
	}
}


bool unify_rus(System& rus) {
	try {
		if (rus.config.verbose) cout << "verifying russell source ... " << flush;
		rus.timers["unify"].start();
		uint lab = Lex::toInt(rus.config.in);
		verify(rus.math.sources[lab]);
		rus.timers["unify"].stop();
		if (rus.config.verbose) cout << "done in " << rus.timers["unify"] << endl;
		return true;
	} catch (Error& err) {
		rus.error += '\n';
		rus.error += err.what();
		return false;
	}
}

bool translate_rus(System& rus) {
	try {
		if (rus.config.out.empty()) return true;
		if (rus.config.verbose) cout << "translating file " << rus.config.in << " ... " << flush;
		rus.timers["translate"].start();
		uint lab = Lex::toInt(rus.config.in);
		smm::Source* target = translate(rus.math.sources[lab]);
		if (rus.config.deep) {
			deep_write(
				target,
				[](smm::Source* src) -> vector<smm::Node>& { return src->contents; },
				[](smm::Node n) -> smm::Source* { return n.val.inc->source; },
				[](smm::Node n) -> bool { return n.type == smm::Node::INCLUSION; }
			);
		} else {
			//shallow_write(target);
			ofstream out(rus.config.out);
			out << *target << endl;
			out.close();
		}
		delete target;
		rus.timers["translate"].stop();
		if (rus.config.verbose) cout << "done in " << rus.timers["translate"] << endl;
		return true;
	} catch (Error& err) {
		rus.error += '\n';
		rus.error += err.what();
		return false;
	}
}

bool write_rus(System& rus) {
	try {
		if (rus.config.out.empty()) return true;
		if (rus.config.verbose) cout << "replicating file " << rus.config.in << " ... " << flush;
		rus.timers["write"].start();
		ofstream out(rus.config.out);
		uint lab = Lex::toInt(rus.config.in);
		out << *rus.math.sources[lab] << endl;
		out.close();
		rus.timers["write"].stop();
		if (rus.config.verbose) cout << "done in " << rus.timers["write"] << endl;
		return true;
	} catch (Error& err) {
		rus.error += '\n';
		rus.error += err.what();
		return false;
	}
}

}

void run(System& sys) {
	sys.timers["total"].start();
	if (sys.config.verbose)
		cout << "processing file " << sys.config.in << " ... " << endl;
	if (!parse_rus(sys)) return;
	if (!parse_exp(sys)) return;
	if (!unify_rus(sys)) return;
	switch (sys.config.mode) {
	case Config::Mode::PROVE:   break;
	case Config::Mode::TRANSL:  break;
	case Config::Mode::MONITOR: break;
	default : break;
	}
	switch (sys.config.target) {
	case Config::Target::RUS: write_rus(sys); break;
	case Config::Target::SMM: translate_rus(sys); break;
	default : break;
	}
	sys.timers["total"].stop();
	if (sys.config.verbose)
		cout << "all done in " << sys.timers["total"] << endl;
}

string show(const System& rus) {
	return info(rus);
}

string info(const System& sys) {
	string stats;
	stats += "Timings:";
	stats += show_timer("\n\tread:       ", "read", sys.timers);
	stats += show_timer("\n\texpression: ", "expr", sys.timers);
	stats += show_timer("\n\tunify:      ", "unify", sys.timers);
	stats += show_timer("\n\ttranslate:  ", "translate", sys.timers);
	stats += show_timer("\n\twrite:      ", "write", sys.timers);
	stats += stats += "\n";
	stats += show_timer("\n\ttotal: ", "total", sys.timers);
	stats += "\n\n";

	const size_t const_vol = mdl::memvol(sys.math.consts);
	const size_t types_vol = mdl::memvol(sys.math.types);
	const size_t rules_vol = mdl::memvol(sys.math.rules);
	const size_t axiom_vol = mdl::memvol(sys.math.axioms);
	const size_t defs_vol  = mdl::memvol(sys.math.defs);
	const size_t thems_vol = mdl::memvol(sys.math.theorems);
	const size_t proof_vol = mdl::memvol(sys.math.proofs);
	uint lab = Lex::toInt(sys.config.in);
	const size_t source_vol = memvol(*sys.math.sources.at(lab));
	const size_t total_vol =
		const_vol + types_vol + rules_vol +
		axiom_vol + defs_vol + thems_vol + proof_vol;

	stats += "Volume:\n";
	stats += "\tconsts:   " + showmem(const_vol) + "\n";
	stats += "\ttypes:    " + showmem(types_vol) + "\n";
	stats += "\trules:    " + showmem(rules_vol) + "\n";
	stats += "\taxioms:   " + showmem(axiom_vol) + "\n";
	stats += "\tdefs:     " + showmem(defs_vol) + "\n";
	stats += "\ttheorems: " + showmem(thems_vol) + "\n";
	stats += "\tproofs:   " + showmem(proof_vol) + "\n";
	stats += "\n";
	stats += "\ttotal:  " + showmem(total_vol) + "\n";
	stats += "\tsource: " + showmem(source_vol) + "\n";
	stats += "\n";

	stats += "Size:\n";
	stats += "\tconsts:   " + to_string(sys.math.consts.size()) + "\n";
	stats += "\ttypes:    " + to_string(sys.math.types.size()) + "\n";
	stats += "\trules:    " + to_string(sys.math.rules.size()) + "\n";
	stats += "\taxioms:   " + to_string(sys.math.axioms.size()) + "\n";
	stats += "\tdefs:     " + to_string(sys.math.defs.size()) + "\n";
	stats += "\ttheorems: " + to_string(sys.math.theorems.size()) + "\n";
	stats += "\tproofs:   " + to_string(sys.math.proofs.size()) + "\n";
	stats += "\n";

	return stats;
}

}} // mdl::rus

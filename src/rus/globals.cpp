#include "rus/globals.hpp"

namespace mdl {

string show_sy(Symbol symb) {
	return rus::System::get().lex.symbs.toStr(symb.lit);
}
string show_id(uint lab) {
	return rus::System::get().lex.ids.toStr(lab);
}

namespace rus { namespace {

bool parse_rus(System& rus) {
	try {
		if (rus.config.verbose) cout << "parsing russell source ... " << flush;
		rus.timers.parse_rus.start();
		rus.source = parse(rus.config.in);
		rus.timers.parse_rus.stop();
		if (rus.config.verbose) cout << "done in " << rus.timers.parse_rus << endl;
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
		rus.timers.parse_expr.start();
		expr::parse();
		rus.timers.parse_expr.stop();
		if (rus.config.verbose) cout << "done in " << rus.timers.parse_expr << endl;
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
		rus.timers.unify.start();
		verify(rus.source);
		rus.timers.unify.stop();
		if (rus.config.verbose) cout << "done in " << rus.timers.unify << endl;
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
		rus.timers.translate.start();
		smm::Source* target = translate(rus.source);
		if (rus.config.deep) {
			deep_write(
				target,
				[](smm::Source* src) -> vector<smm::Node>& { return src->contents; },
				[](smm::Node n) -> smm::Source* { return n.val.inc->source; },
				[](smm::Node n) -> bool { return n.type == smm::Node::INCLUSION; }
			);
		} else {
			ofstream out(rus.config.out);
			out << *target << endl;
			out.close();
		}
		delete target;
		rus.timers.translate.stop();
		if (rus.config.verbose) cout << "done in " << rus.timers.translate << endl;
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
		rus.timers.translate.start();
		ofstream out(rus.config.out);
		out << *rus.source << endl;
		out.close();
		rus.timers.translate.stop();
		if (rus.config.verbose) cout << "done in " << rus.timers.translate << endl;
		return true;
	} catch (Error& err) {
		rus.error += '\n';
		rus.error += err.what();
		return false;
	}
}

}

void System::run() {
	timers.total.start();
	if (config.verbose)
		cout << "processing file " << config.in << " ... " << endl;
	if (!parse_rus(*this)) return;
	if (!parse_exp(*this)) return;
	if (!unify_rus(*this)) return;
	switch (config.mode) {
	case Config::Mode::PROVE:   break;
	case Config::Mode::TRANSL:  break;
	case Config::Mode::MONITOR: break;
	default : break;
	}
	switch (config.target) {
	case Config::Target::RUS: write_rus(*this); break;
	case Config::Target::SMM: translate_rus(*this); break;
	default : break;
	}
	timers.total.stop();
	if (config.verbose)
		cout << "all done in " << timers.total << endl;
}

string show(const System& rus) {
	string stats;
	stats += "Timings\n";
	stats += "\tparse rus:  " + show(rus.timers.parse_rus) + "\n";
	stats += "\tparse expr: " + show(rus.timers.parse_expr) + "\n";
	stats += "\tunify:      " + show(rus.timers.unify) + "\n";
	stats += "\ttranslate:  " + show(rus.timers.translate) + "\n";
	stats += "\n";
	stats += "\ttotal: " + show(rus.timers.total) + "\n";
	stats += "\n";

	const size_t const_vol = mdl::memvol(rus.math.consts);
	const size_t types_vol = mdl::memvol(rus.math.types);
	const size_t rules_vol = mdl::memvol(rus.math.rules);
	const size_t axiom_vol = mdl::memvol(rus.math.axioms);
	const size_t defs_vol  = mdl::memvol(rus.math.defs);
	const size_t thems_vol = mdl::memvol(rus.math.theorems);
	const size_t proof_vol = mdl::memvol(rus.math.proofs);
	const size_t source_vol = memvol(*rus.source);
	const size_t total_vol =
		const_vol + types_vol + rules_vol +
		axiom_vol + defs_vol + thems_vol + proof_vol;

	stats += "Volume\n";
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

	stats += "Size\n";
	stats += "\tconsts:   " + to_string(rus.math.consts.size()) + "\n";
	stats += "\ttypes:    " + to_string(rus.math.types.size()) + "\n";
	stats += "\trules:    " + to_string(rus.math.rules.size()) + "\n";
	stats += "\taxioms:   " + to_string(rus.math.axioms.size()) + "\n";
	stats += "\tdefs:     " + to_string(rus.math.defs.size()) + "\n";
	stats += "\ttheorems: " + to_string(rus.math.theorems.size()) + "\n";
	stats += "\tproofs:   " + to_string(rus.math.proofs.size()) + "\n";
	stats += "\n";

	return stats;
}

}} // mdl::rus

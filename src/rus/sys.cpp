#include "rus/sys.hpp"

namespace mdl { namespace rus { namespace {

bool parse_rus() {
	try {
		if (System::conf().verbose) cout << "parsing russell source ... " << flush;
		System::timer()["read"].start();
		parse(System::conf().in);
		System::timer()["read"].stop();
		if (System::conf().verbose) cout << "done in " << System::timer()["read"] << endl;
		return true;
	} catch (Error& err) {
		System::io().err() << err.what() << endl;
		return false;
	}
}

bool parse_exp() {
	try {
		if (System::conf().verbose) cout << "parsing expressions ... " << flush;
		System::timer()["expr"].start();
		expr::parse();
		System::timer()["expr"].stop();
		if (System::conf().verbose) cout << "done in " << System::timer()["expr"] << endl;
		return true;
	} catch (Error& err) {
		System::io().err() << err.what() << endl;
		return false;
	}
}


bool unify_rus() {
	try {
		if (System::conf().verbose) cout << "verifying russell source ... " << flush;
		System::timer()["unify"].start();
		uint lab = Lex::toInt(System::conf().in.name);
		verify(System::get().math.sources.at(lab));
		System::timer()["unify"].stop();
		if (System::conf().verbose) cout << "done in " << System::timer()["unify"] << endl;
		return true;
	} catch (Error& err) {
		System::io().err() << err.what() << endl;
		return false;
	}
}

bool translate_rus() {
	try {
		if (System::conf().out.name.empty()) return true;
		if (System::conf().verbose) cout << "translating file " << System::conf().in.name << " ... " << flush;
		System::timer()["translate"].start();
		uint lab = Lex::toInt(System::conf().in.name);
		smm::Source* target = translate(System::get().math.sources.at(lab));
		if (System::conf().deep) {
			deep_write(
				target,
				[](smm::Source* src) -> vector<smm::Node>& { return src->contents; },
				[](smm::Node n) -> smm::Source* { return n.val.inc->source; },
				[](smm::Node n) -> bool { return n.type == smm::Node::INCLUSION; }
			);
		} else {
			shallow_write(target);
		}
		System::timer()["translate"].stop();
		if (System::conf().verbose) cout << "done in " << System::timer()["translate"] << endl;
		return true;
	} catch (Error& err) {
		System::io().err() << err.what() << endl;
		return false;
	}
}

bool write_rus() {
	try {
		if (System::conf().out.name.empty()) return true;
		if (System::conf().verbose) cout << "replicating file " << System::conf().out.name << " ... " << flush;
		System::timer()["write"].start();
		ofstream out(System::conf().out.path());
		uint lab = Lex::toInt(System::conf().out.name);
		out << *System::get().math.sources.at(lab) << endl;
		out.close();
		System::timer()["write"].stop();
		if (System::conf().verbose) cout << "done in " << System::timer()["write"] << endl;
		return true;
	} catch (Error& err) {
		System::io().err() << err.what() << endl;
		return false;
	}
}

}

void run() {
	System::timer()["total"].start();
	if (System::conf().verbose)
		cout << "processing file " << System::conf().in.name << " ... " << endl;
	if (!parse_rus()) return;
	if (!parse_exp()) return;
	if (!unify_rus()) return;
	switch (System::conf().mode) {
	case Config::Mode::PROVE:   break;
	case Config::Mode::TRANSL:  break;
	case Config::Mode::MONITOR: break;
	default : break;
	}
	switch (System::conf().target) {
	case Config::Target::RUS: write_rus(); break;
	case Config::Target::SMM: translate_rus(); break;
	default : break;
	}
	System::timer()["total"].stop();
	if (System::conf().verbose)
		cout << "all done in " << System::timer()["total"] << endl;
}

string show() {
	return info();
}

string info() {
	string stats;
	stats += "Timings:";
	stats += show_timer("\n\tread:       ", "read", System::timer());
	stats += show_timer("\n\texpression: ", "expr", System::timer());
	stats += show_timer("\n\tunify:      ", "unify", System::timer());
	stats += show_timer("\n\ttranslate:  ", "translate", System::timer());
	stats += show_timer("\n\twrite:      ", "write", System::timer());
	stats += stats += "\n";
	stats += show_timer("\n\ttotal: ", "total", System::timer());
	stats += "\n\n";

	const size_t const_vol = mdl::memvol(System::get().math.consts);
	const size_t types_vol = mdl::memvol(System::get().math.types);
	const size_t rules_vol = mdl::memvol(System::get().math.rules);
	const size_t axiom_vol = mdl::memvol(System::get().math.axioms);
	const size_t defs_vol  = mdl::memvol(System::get().math.defs);
	const size_t thems_vol = mdl::memvol(System::get().math.theorems);
	const size_t proof_vol = mdl::memvol(System::get().math.proofs);
	uint lab = Lex::toInt(System::conf().in.name);
	const size_t source_vol = memvol(*System::get().math.sources.at(lab));
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
	stats += "\tconsts:   " + to_string(System::get().math.consts.size()) + "\n";
	stats += "\ttypes:    " + to_string(System::get().math.types.size()) + "\n";
	stats += "\trules:    " + to_string(System::get().math.rules.size()) + "\n";
	stats += "\taxioms:   " + to_string(System::get().math.axioms.size()) + "\n";
	stats += "\tdefs:     " + to_string(System::get().math.defs.size()) + "\n";
	stats += "\ttheorems: " + to_string(System::get().math.theorems.size()) + "\n";
	stats += "\tproofs:   " + to_string(System::get().math.proofs.size()) + "\n";
	stats += "\n";

	return stats;
}

}} // mdl::rus

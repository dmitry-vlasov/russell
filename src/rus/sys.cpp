#include "rus/sys.hpp"

namespace mdl { namespace rus { namespace {

bool parse_rus() {
	try {
		if (Sys::conf().verbose) cout << "parsing russell source ... " << flush;
		Sys::timer()["read"].start();
		parse(Sys::conf().in);
		Sys::timer()["read"].stop();
		if (Sys::conf().verbose) cout << "done in " << Sys::timer()["read"] << endl;
		return true;
	} catch (Error& err) {
		Sys::io().err() << err.what() << endl;
		return false;
	}
}

bool parse_exp() {
	try {
		if (Sys::conf().verbose) cout << "parsing expressions ... " << flush;
		Sys::timer()["expr"].start();
		expr::parse();
		Sys::timer()["expr"].stop();
		if (Sys::conf().verbose) cout << "done in " << Sys::timer()["expr"] << endl;
		return true;
	} catch (Error& err) {
		Sys::io().err() << err.what() << endl;
		return false;
	}
}


bool unify_rus() {
	try {
		if (Sys::conf().verbose) cout << "verifying russell source ... " << flush;
		Sys::timer()["unify"].start();
		uint lab = Lex::toInt(Sys::conf().in.name);
		verify(Sys::get().math.sources.at(lab));
		Sys::timer()["unify"].stop();
		if (Sys::conf().verbose) cout << "done in " << Sys::timer()["unify"] << endl;
		return true;
	} catch (Error& err) {
		Sys::io().err() << err.what() << endl;
		return false;
	}
}

bool translate_rus() {
	try {
		if (Sys::conf().out.name.empty()) return true;
		if (Sys::conf().verbose) cout << "translating file " << Sys::conf().in.name << " ... " << flush;
		Sys::timer()["translate"].start();
		uint lab = Lex::toInt(Sys::conf().in.name);
		smm::Source* target = translate(Sys::get().math.sources.at(lab));
		if (Sys::conf().deep) {
			deep_write(
				target,
				[](smm::Source* src) -> vector<smm::Node>& { return src->contents; },
				[](smm::Node n) -> smm::Source* { return n.val.inc->source; },
				[](smm::Node n) -> bool { return n.type == smm::Node::INCLUSION; }
			);
		} else {
			shallow_write(target);
		}
		Sys::timer()["translate"].stop();
		if (Sys::conf().verbose) cout << "done in " << Sys::timer()["translate"] << endl;
		return true;
	} catch (Error& err) {
		Sys::io().err() << err.what() << endl;
		return false;
	}
}

bool write_rus() {
	try {
		if (Sys::conf().out.name.empty()) return true;
		if (Sys::conf().verbose) cout << "replicating file " << Sys::conf().out.name << " ... " << flush;
		Sys::timer()["write"].start();
		ofstream out(Sys::conf().out.path());
		uint lab = Lex::toInt(Sys::conf().out.name);
		out << *Sys::get().math.sources.at(lab) << endl;
		out.close();
		Sys::timer()["write"].stop();
		if (Sys::conf().verbose) cout << "done in " << Sys::timer()["write"] << endl;
		return true;
	} catch (Error& err) {
		Sys::io().err() << err.what() << endl;
		return false;
	}
}

}

void run() {
	Sys::timer()["total"].start();
	if (Sys::conf().verbose)
		cout << "processing file " << Sys::conf().in.name << " ... " << endl;
	if (!parse_rus()) return;
	if (!parse_exp()) return;
	if (!unify_rus()) return;
	switch (Sys::conf().mode) {
	case Mode::PROVE:   break;
	case Mode::TRANSL:  break;
	default : break;
	}
	switch (Sys::conf().target) {
	case Lang::RUS: write_rus(); break;
	case Lang::SMM: translate_rus(); break;
	default : break;
	}
	Sys::timer()["total"].stop();
	if (Sys::conf().verbose)
		cout << "all done in " << Sys::timer()["total"] << endl;
}

string show() {
	return info();
}

string info() {
	string stats;
	stats += "Timings:";
	stats += show_timer("\n\tread:       ", "read", Sys::timer());
	stats += show_timer("\n\texpression: ", "expr", Sys::timer());
	stats += show_timer("\n\tunify:      ", "unify", Sys::timer());
	stats += show_timer("\n\ttranslate:  ", "translate", Sys::timer());
	stats += show_timer("\n\twrite:      ", "write", Sys::timer());
	stats += stats += "\n";
	stats += show_timer("\n\ttotal: ", "total", Sys::timer());
	stats += "\n\n";

	const size_t const_vol = mdl::memvol(Sys::get().math.consts);
	const size_t types_vol = mdl::memvol(Sys::get().math.types);
	const size_t rules_vol = mdl::memvol(Sys::get().math.rules);
	const size_t axiom_vol = mdl::memvol(Sys::get().math.axioms);
	const size_t defs_vol  = mdl::memvol(Sys::get().math.defs);
	const size_t thems_vol = mdl::memvol(Sys::get().math.theorems);
	const size_t proof_vol = mdl::memvol(Sys::get().math.proofs);
	uint lab = Lex::toInt(Sys::conf().in.name);
	const size_t source_vol = memvol(*Sys::get().math.sources.at(lab));
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
	stats += "\tconsts:   " + to_string(Sys::get().math.consts.size()) + "\n";
	stats += "\ttypes:    " + to_string(Sys::get().math.types.size()) + "\n";
	stats += "\trules:    " + to_string(Sys::get().math.rules.size()) + "\n";
	stats += "\taxioms:   " + to_string(Sys::get().math.axioms.size()) + "\n";
	stats += "\tdefs:     " + to_string(Sys::get().math.defs.size()) + "\n";
	stats += "\ttheorems: " + to_string(Sys::get().math.theorems.size()) + "\n";
	stats += "\tproofs:   " + to_string(Sys::get().math.proofs.size()) + "\n";
	stats += "\n";

	return stats;
}

Sys::Sys() {

}

}} // mdl::rus
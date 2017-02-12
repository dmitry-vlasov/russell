#include "../../include/rus/sys.hpp"

namespace mdl {

string show_sy(Symbol symb) {
	return rus::Sys::get().lex.symbols.toStr(symb.lit);
}
string show_id(uint lab) {
	return rus::Sys::get().lex.labels.toStr(lab);
}

namespace rus {

Source* parse(string name);

bool parse_rus(Sys& rus) {
	try {
		if (Sys::conf().verbose) cout << "parsing russell source ... " << flush;
		Sys::timer()["read"].start();
		rus.source = rus::parse(Sys::conf().in);
		Sys::timer()["read"].stop();
		if (Sys::conf().verbose) cout << "done in " << Sys::timer()["read"] << endl;
		return true;
	} catch (Error& err) {
		Sys::io().err << '\n';
		Sys::io().err << err.what();
		return false;
	}
}

bool parse_exp(Sys& rus) {
	try {
		if (Sys::conf().verbose) cout << "parsing expressions ... " << flush;
		Sys::timer()["expr"].start();
		expr::parse();
		Sys::timer()["expr"].stop();
		if (Sys::conf().verbose) cout << "done in " << Sys::timer()["expr"] << endl;
		return true;
	} catch (Error& err) {
		Sys::io().err << '\n';
		Sys::io().err << err.what();
		return false;
	}
}


bool Sys::read(const string& path) {
	if (!parse_rus(*this)) return false;
	if (!parse_exp(*this)) return false;
}

bool Sys::write(const string& path) {

}

void verify(Source* source);

bool Sys::verify(const string& path) {
	try {
		if (Sys::conf().verbose) cout << "verifying russell source ... " << flush;
		Sys::timer()["unify"].start();
		rus::verify(source);
		Sys::timer()["unify"].stop();
		if (Sys::conf().verbose) cout << "done in " << Sys::timer()["unify"] << endl;
		return true;
	} catch (Error& err) {
		Sys::io().err << '\n';
		Sys::io().err << err.what();
		return false;
	}
}


bool unify_rus(Sys& rus) {
	try {
		if (Sys::conf().verbose) cout << "verifying russell source ... " << flush;
		Sys::timer()["unify"].start();
		verify(rus.source);
		Sys::timer()["unify"].stop();
		if (Sys::conf().verbose) cout << "done in " << Sys::timer()["unify"] << endl;
		return true;
	} catch (Error& err) {
		Sys::io().err << '\n';
		Sys::io().err << err.what();
		return false;
	}
}

bool translate_rus(Sys& rus) {
	try {
		if (Sys::conf().out.empty()) return true;
		if (Sys::conf().verbose) cout << "translating file " << Sys::conf().in << " ... " << flush;
		Sys::timer()["translate"].start();
		smm::Source* target = translate(rus.source);
		if (Sys::conf().deep) {
			deep_write(
				target,
				[](smm::Source* src) -> vector<smm::Node>& { return src->contents; },
				[](smm::Node n) -> smm::Source* { return n.val.inc->source; },
				[](smm::Node n) -> bool { return n.type == smm::Node::INCLUSION; }
			);
		} else {
			ofstream out(Sys::conf().out);
			out << *target << endl;
			out.close();
		}
		delete target;
		Sys::timer()["translate"].stop();
		if (Sys::conf().verbose) cout << "done in " << Sys::timer()["translate"] << endl;
		return true;
	} catch (Error& err) {
		Sys::io().err << '\n';
		Sys::io().err << err.what();
		return false;
	}
}

bool write_rus(Sys& rus) {
	try {
		if (Sys::conf().out.empty()) return true;
		if (Sys::conf().verbose) cout << "replicating file " << Sys::conf().in << " ... " << flush;
		Sys::timer()["write"].start();
		ofstream out(Sys::conf().out);
		out << *rus.source << endl;
		out.close();
		Sys::timer()["write"].stop();
		if (Sys::conf().verbose) cout << "done in " << Sys::timer()["write"] << endl;
		return true;
	} catch (Error& err) {
		Sys::io().err << '\n';
		Sys::io().err << err.what();
		return false;
	}
}

void run(Sys& sys) {
	Sys::timer()["total"].start();
	if (Sys::conf().verbose)
		cout << "processing file " << Sys::conf().in << " ... " << endl;
	if (!parse_rus(sys)) return;
	if (!parse_exp(sys)) return;
	if (!unify_rus(sys)) return;
	switch (Sys::conf().mode) {
	case Config::Mode::PROVE:   break;
	case Config::Mode::TRANSL:  break;
	case Config::Mode::MONITOR: break;
	default : break;
	}
	switch (Sys::conf().target) {
	case Config::Target::RUS: write_rus(sys); break;
	case Config::Target::SMM: translate_rus(sys); break;
	default : break;
	}
	Sys::timer()["total"].stop();
	if (Sys::conf().verbose)
		cout << "all done in " << Sys::timer()["total"] << endl;
}

string Sys::show() const {
	return info();
}

string Sys::info() const {
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

	const size_t const_vol = mdl::memvol(math.consts);
	const size_t types_vol = mdl::memvol(math.types);
	const size_t rules_vol = mdl::memvol(math.rules);
	const size_t axiom_vol = mdl::memvol(math.axioms);
	const size_t defs_vol  = mdl::memvol(math.defs);
	const size_t thems_vol = mdl::memvol(math.theorems);
	const size_t proof_vol = mdl::memvol(math.proofs);
	const size_t source_vol = memvol(*source);
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
	stats += "\tconsts:   " + to_string(math.consts.size()) + "\n";
	stats += "\ttypes:    " + to_string(math.types.size()) + "\n";
	stats += "\trules:    " + to_string(math.rules.size()) + "\n";
	stats += "\taxioms:   " + to_string(math.axioms.size()) + "\n";
	stats += "\tdefs:     " + to_string(math.defs.size()) + "\n";
	stats += "\ttheorems: " + to_string(math.theorems.size()) + "\n";
	stats += "\tproofs:   " + to_string(math.proofs.size()) + "\n";
	stats += "\n";

	return stats;
}

}} // mdl::rus

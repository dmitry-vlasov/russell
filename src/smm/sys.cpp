#include <boost/filesystem.hpp>

#include "smm/sys.hpp"
#include "smm/parser.hpp"

namespace mdl {

string show_sy(Symbol symb) {
	return smm::Sys::get().lex.symbols.toStr(symb.lit);
}
string show_id(uint lab) {
	return smm::Sys::get().lex.labels.toStr(lab);
}

namespace smm {

uint validate(const string& name) {
	Path path = Sys::mod().conf().in.relative(name).open();
	return Sys::mod().lex.labels.toInt(path.name);
}
/*
bool Sys::read(const string& path) {
	typedef parser::Grammar<LocationIter> Parser;
	Sys::timer()["read"].start();
	source = mdl::parse<Source, Parser>(Sys::conf().in, Sys::conf().root, parser::ascii::space);
	Sys::timer()["read"].stop();
	return true;
}

void verify(const vector<Assertion*>& theory);

bool Sys::verify(const string& path) {
	try {
		Sys::timer()["verify"].start();
		smm::verify(math.assertions);
		Sys::timer()["verify"].stop();
		return true;
	} catch (Error& err) {
		Sys::io().err << err.what();
		return false;
	}
}

bool Sys::write(const string& path) {
	//typedef parser::Grammar<LocationIter> Parser;
	//Sys::timer()["read"].start();
	//source = mdl::parse<Source, Parser>(Sys::conf().in, Sys::conf().root, parser::ascii::space);
	//Sys::timer()["read"].stop();
	return true;
}

string Sys::show() const {
	return info();
}

string Sys::info() const {
	string stats;
	if (Sys::io().err.str().size()) stats += "error:\n" + Sys::io().err.str() + "\n\n";
	stats += "Timings:";
	stats += show_timer("\n\tread:      ", "read", Sys::timer());
	stats += show_timer("\n\tverify:    ", "verify", Sys::timer());
	stats += show_timer("\n\ttranslate: ", "translate", Sys::timer());
	stats += show_timer("\n\ttotal:     ", "total", Sys::timer());
	stats += "\n\n";
	stats += "Size:\n";
	stats += "\tconstants:  " + to_string(math.constants.size()) + "\n";
	stats += "\tassertions: " + to_string(math.assertions.size()) + "\n";
	stats += "\n";
	return stats;
}


static bool translate(Sys& sys) {
	try {
		if (Sys::conf().out.empty()) return true;
		if (Sys::conf().verbose)
			cout << "translating file " << Sys::conf().in << " ... " << flush;
		Sys::timer()["translate"].start();
		switch (Sys::conf().target) {
		case Config::Target::TARGET_NONE: break;
		case Config::Target::TARGET_MM: {
			mm::Source* target = smm::translate_to_mm(sys.source);
			if (Sys::conf().deep) {
				deep_write(
					target,
					[](mm::Source* src) -> vector<mm::Node>& { return src->block->contents; },
					[](mm::Node n) -> mm::Source* { return n.val.inc->source; },
					[](mm::Node n) -> bool { return n.type == mm::Node::INCLUSION; }
				);
			} else {
				ofstream out(Sys::conf().out);
				out << *target << endl;
				out.close();
			}
			delete target;
		}	break;
		case Config::Target::TARGET_RUS: {
			rus::Source* target = smm::translate_to_rus(sys.source);
			if (Sys::conf().deep) {
				deep_write(
					target,
					[](rus::Source* src) -> vector<rus::Node>& { return src->theory->nodes; },
					[](rus::Node n) -> rus::Source* { return n.val.imp->source; },
					[](rus::Node n) -> bool { return n.kind == rus::Node::IMPORT; }
				);
			} else {
				ofstream out(Sys::conf().out);
				out << *target << endl;
				out.close();
			}
			delete target;
		}	break;
		}
		Sys::timer()["translate"].stop();
		if (Sys::conf().verbose)
			cout << "done in " << Sys::timer()["translate"] << endl;
		return true;
	} catch (Error& err) {
		Sys::io().err << err.what();
		return false;
	}
}

void run(Sys& sys) {
	Sys::timer()["total"].start();
	if (Sys::conf().verbose)
		cout << "verifying file " << Sys::conf().in << " ... " << endl;
	if (!sys.read(Sys::conf().in))     return;
	if (!sys.verify(Sys::conf().in))   return;
	if (!translate(sys)) return;
	Sys::timer()["total"].stop();
	if (Sys::conf().verbose)
		cout << "all done in " << Sys::timer()["total"] << endl;
}
	
Return read(const Args& args) {
	try {
		string name = args[0];
		uint label = sys->lex.labels.toInt(name);
		if (!sys->math.sources.has(label)) {
			Sys::timer()["read"].start();
			Source* source = parse(Sys::conf().in.relative(name));
			if (!source) throw Error("parsing of " + name + " failed");
			Sys::timer()["read"].stop();
			return Return("success", any(source));
		} else {
			return Return("failure: " + name + " already is read");
		}
	} catch (Error& err) {
		return Return(string("failure: ") + err.what());
	}
}
*/

void spirit_parse(uint label);

Sys::Sys(const string& name) : mdl::Sys<Sys, Source, Math, Config>(name) {
	action["read"] =
		[](const Args& args) {
			try {
				string name = args[0];
				uint label = validate(name);
				if (!Sys::get().math.sources.has(label)) {
					Sys::timer()["read"].start();
					spirit_parse(label);
					Sys::timer()["read"].stop();
					return Return("success", Sys::mod().math.sources.access(label));
				} else {
					return Return("failure: " + name + " already is read");
				}
			} catch (Error& err) {
				return Return(string("failure: ") + err.what());
			}
		};
}

}} // mdl::smm

#include <boost/filesystem.hpp>

#include "../../include/mm/sys.hpp"
#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "cut/ast.hpp"
#include "merge/ast.hpp"

namespace mdl {

string show_sy(Symbol symb) {
	return mm::Sys::get().lex.symbols.toStr(symb.lit);
}
string show_id(uint lab) {
	return mm::Sys::get().lex.labels.toStr(lab);
}

namespace mm {

/*
bool parse_mm(Sys& mm) {
	try {
		Sys::timer()["read"].start();
		mm.source = parse(Sys::conf().in);
		if (!mm.source) throw Error("parsing of " + Sys::conf().in + " failed");
		//cout << endl << *source;
		Sys::timer()["read"].stop();
		return true;
	} catch (Error& err) {
		Sys::io().err << err.what();
		return false;
	}
}

bool cut_mm(Sys& mm) {
	try {
		Sys::timer()["work"].start();
		cut::Section* source = cut::parse(Sys::conf().root, Sys::conf().in, Sys::conf().out);
		cut::split(source);
		cut::save(source);
		delete source;
		Sys::timer()["work"].stop();
		return true;
	} catch (Error& err) {
		Sys::io().err << err.what();
		return false;
	}
}

bool merge_mm(Sys& mm) {
	try {
		Sys::timer()["work"].start();
		merge::parse(Sys::conf().in);
		ofstream out(Sys::conf().out);
		out << merge::Source::get().contents.str();
		out.close();
		Sys::timer()["work"].stop();
		return true;
	} catch (Error& err) {
		Sys::io().err << err.what();
		return false;
	}
}

inline Source* find_source(const string& name) {
	if (name.size()) {
		uint lab = Sys::get().lex.labels.getInt(name);
		return Sys::get().math.sources.[lab];
	} else {
		return Sys::get().source;
	}
}

smm::Sys Sys::translate(const string& name) const {
	smm::Sys sys("translated");
	try {
		if (conf().out.empty()) {
			io().err << "output file is not specified";
			return false;
		}
		timer()["work"].start();
		Source* src = find_source(name);
		sys.source = translate(src);
		timer()["work"].stop();
		return sys;
	} catch (Error& err) {
		Sys::io().err << err.what();
		return sys;
	}
}


bool translate_mm(Sys& mm) {
	if (smm::Source* target = sys.translate()) {
		delete target;
		return true;
	}
	return false;
}

Return Read::operator()(const many& vars) {
	try {
		uint label = Undef<uint>::get();
		string name = "";
		if (vars[0].type() == typeid(int)) {
			label = boost::any_cast<uint>(vars[0]);
			name = sys->lex.labels.toStr(label);
		} else if (vars[0].type() == typeid(string)) {
			name = boost::any_cast<string>(vars[0]);
			label = sys->lex.labels.toInt(name);
		} else {
			return Return(string("failure: wrong argument type ") + vars[0].type().name());
		}
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

Return Erase::operator()(const many& vars) {
	try {
		uint label = Undef<uint>::get();
		string name = "";
		if (vars[0].type() == typeid(int)) {
			label = boost::any_cast<uint>(vars[0]);
			name = sys->lex.labels.toStr(label);
		} else if (vars[0].type() == typeid(string)) {
			name = boost::any_cast<string>(vars[0]);
			label = sys->lex.labels.toInt(name);
		} else {
			return Return(string("failure: wrong argument type ") + vars[0].type().name());
		}
		if (sys->math.sources.has(label)) {
			Sys::timer()["erase"].start();
			sys->math.sources.clear(label);
			Sys::timer()["erase"].stop();
			return Return("success");
		} else {
			return Return("failure: " + name + " file is not read");
		}
	} catch (Error& err) {
		return Return(string("failure: ") + err.what());
	}
}

Sys& Sys::read(const string& name) {
	Source* src = find_source(name);
	Sys::timer()["read"].start();
	source = parse(Sys::conf().in);
	if (!source) throw Error("parsing of " + Sys::conf().in + " failed");
	Sys::timer()["read"].stop();
	return *this;
}

Sys& Sys::write(const string& name) {
	Source* src = find_source(name);
	if (Sys::conf().deep) {
		deep_write(
			src,
			[](Source* src) -> vector<Node>& { return src->theory->nodes; },
			[](Node n) -> Source* { return n.val.imp->source; },
			[](Node n) -> bool { return n.kind == Node::IMPORT; }
		);
	} else {
		shallow_write(src);
	}
	return *this;
}

Sys& Sys::verify(const string& name) {
	Source* src = find_source(name);
	return *this;
}

string Sys::show() const {
	return info();
}

string Sys::info() const {
	string stats;
	stats += "Timings:";
	stats += show_timer("\n\tread:  ", "read", Sys::timer());
	stats += show_timer("\n\twork:  ", "work", Sys::timer());
	stats += show_timer("\n\ttotal: ", "total", Sys::timer());
	stats += "\n\n";
	stats += "Size:\n";
	stats += "\taxioms:     " + to_string(math.axioms.size()) + "\n";
	stats += "\ttheorems:   " + to_string(math.theorems.size()) + "\n";
	stats += "\tessentials: " + to_string(math.essentials.size()) + "\n";
	stats += "\tfloatings:  " + to_string(math.floatings.size()) + "\n";
	stats += "\n";
	return stats;
}

void Sys::run() {
	timer()["total"].start();
	if (conf().verbose) io().out() << "processing file " << Sys::conf().in.name << " ... " << flush;
	switch (conf().mode) {
	case Config::Mode::CUT:    cut(conf().in).split().save(); break;
	case Config::Mode::MERGE:  merge(conf().in).save();       break;
	case Config::Mode::TRANSL: read(conf().in).translate(conf().out).write(); break;
	default : break;
	}
	timer()["total"].stop();
	if (conf().verbose) io().out() << "done in " << Sys::timer()["total"] << endl;
}
*/

uint validate(const string& name) {
	Path path = Sys::mod().conf().in.relative(name).open();
	return Sys::mod().lex.labels.toInt(path.name);
}

void spirit_parse(uint label);
void peg_parse(uint label);

Return read(const Args& args) {
	try {
		string name = args[0];
		uint label = validate(name);
		if (!Sys::get().math.sources.has(label)) {
			Sys::timer()["read"].start();
			peg_parse(label);
			Sys::timer()["read"].stop();
			return Return("success", Sys::mod().math.sources.access(label));
		} else {
			return Return("failure: " + name + " already is read");
		}
	} catch (Error& err) {
		return Return(string("failure: ") + err.what());
	}
}

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

}} // mdl::mm

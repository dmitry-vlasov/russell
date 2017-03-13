#include <boost/filesystem.hpp>

#include "mm/sys.hpp"
#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "cut/ast.hpp"
#include "merge/ast.hpp"

namespace mdl { namespace mm  { namespace {

bool do_parse() {
	try {
		Sys::timer()["read"].start();
		if (!parse(Sys::conf().in))
			throw Error("parsing of " + Sys::conf().in.name + " failed");
		//cout << endl << *source;
		Sys::timer()["read"].stop();
		return true;
	} catch (Error& err) {
		Sys::io().err() << err.what() << endl;
		return false;
	}
}

bool do_cut() {
	try {
		Sys::timer()["work"].start();
		cut::Section* source = cut::parse(Sys::conf().in.root, Sys::conf().in.path(), Sys::conf().out.root);
		cut::split(source);
		cut::save(source);
		delete source;
		Sys::timer()["work"].stop();
		return true;
	} catch (Error& err) {
		Sys::io().err() << err.what() << endl;
		return false;
	}
}

bool do_merge() {
	try {
		Sys::timer()["work"].start();
		merge::parse(Sys::conf().in.path());
		ofstream out(Sys::conf().out.path());
		out << merge::Source::get().contents.str();
		out.close();
		Sys::timer()["work"].stop();
		return true;
	} catch (Error& err) {
		Sys::io().err() << err.what() << endl;
		return false;
	}
}

bool do_translate() {
	try {
		if (Sys::conf().out.name.empty()) {
			Sys::io().err() << "output file is not specified" << endl;
			return false;
		}
		Sys::timer()["work"].start();
		uint lab = Lex::getInt(Sys::conf().in.name);
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
		Sys::timer()["work"].stop();
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
		cout << "processing file " << Sys::conf().in.name << " ... " << flush;
	if (Sys::conf().mode == Conf::Mode::TRANSL)
		if (!do_parse())
			return;
	//cout << *source << endl;
	switch (Sys::conf().mode) {
	case Conf::Mode::CUT:    do_cut();       break;
	case Conf::Mode::MERGE:  do_merge();     break;
	case Conf::Mode::TRANSL: do_translate(); break;
	default : break;
	}
	Sys::timer()["total"].stop();
	if (Sys::conf().verbose)
		cout << "done in " << Sys::timer()["total"] << endl;
}

string show() {
	return info();
}

string info() {
	string stats;
	stats += "Timings:";
	stats += show_timer("\n\tread:  ", "read", Sys::timer());
	stats += show_timer("\n\twork:  ", "work", Sys::timer());
	stats += show_timer("\n\ttotal: ", "total", Sys::timer());
	stats += "\n\n";
	stats += "Size:\n";
	stats += "\taxioms:     " + to_string(Sys::get().math.axioms.size()) + "\n";
	stats += "\ttheorems:   " + to_string(Sys::get().math.theorems.size()) + "\n";
	stats += "\tessentials: " + to_string(Sys::get().math.essentials.size()) + "\n";
	stats += "\tfloatings:  " + to_string(Sys::get().math.floatings.size()) + "\n";
	stats += "\n";
	return stats;
}


}} // mdl::mm

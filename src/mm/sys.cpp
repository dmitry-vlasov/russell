#include <boost/filesystem.hpp>

#include "mm/sys.hpp"
#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "cut/ast.hpp"
#include "merge/ast.hpp"

namespace mdl { namespace mm  { namespace {

bool do_parse() {
	try {
		System::timer()["read"].start();
		if (!parse(System::conf().in))
			throw Error("parsing of " + System::conf().in.name + " failed");
		//cout << endl << *source;
		System::timer()["read"].stop();
		return true;
	} catch (Error& err) {
		System::io().err() << err.what() << endl;
		return false;
	}
}

bool do_cut() {
	try {
		System::timer()["work"].start();
		cut::Section* source = cut::parse(System::conf().in.root, System::conf().in.path(), System::conf().out.root);
		cut::split(source);
		cut::save(source);
		delete source;
		System::timer()["work"].stop();
		return true;
	} catch (Error& err) {
		System::io().err() << err.what() << endl;
		return false;
	}
}

bool do_merge() {
	try {
		System::timer()["work"].start();
		merge::parse(System::conf().in.path());
		ofstream out(System::conf().out.path());
		out << merge::Source::get().contents.str();
		out.close();
		System::timer()["work"].stop();
		return true;
	} catch (Error& err) {
		System::io().err() << err.what() << endl;
		return false;
	}
}

bool do_translate() {
	try {
		if (System::conf().out.name.empty()) {
			System::io().err() << "output file is not specified" << endl;
			return false;
		}
		System::timer()["work"].start();
		uint lab = Lex::getInt(System::conf().in.name);
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
		System::timer()["work"].stop();
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
		cout << "processing file " << System::conf().in.name << " ... " << flush;
	if (System::conf().mode == Config::Mode::TRANSL)
		if (!do_parse())
			return;
	//cout << *source << endl;
	switch (System::conf().mode) {
	case Config::Mode::CUT:    do_cut();       break;
	case Config::Mode::MERGE:  do_merge();     break;
	case Config::Mode::TRANSL: do_translate(); break;
	default : break;
	}
	System::timer()["total"].stop();
	if (System::conf().verbose)
		cout << "done in " << System::timer()["total"] << endl;
}

string show() {
	return info();
}

string info() {
	string stats;
	stats += "Timings:";
	stats += show_timer("\n\tread:  ", "read", System::timer());
	stats += show_timer("\n\twork:  ", "work", System::timer());
	stats += show_timer("\n\ttotal: ", "total", System::timer());
	stats += "\n\n";
	stats += "Size:\n";
	stats += "\taxioms:     " + to_string(System::get().math.axioms.size()) + "\n";
	stats += "\ttheorems:   " + to_string(System::get().math.theorems.size()) + "\n";
	stats += "\tessentials: " + to_string(System::get().math.essentials.size()) + "\n";
	stats += "\tfloatings:  " + to_string(System::get().math.floatings.size()) + "\n";
	stats += "\n";
	return stats;
}


}} // mdl::mm

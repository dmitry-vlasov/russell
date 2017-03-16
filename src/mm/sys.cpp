#include <boost/filesystem.hpp>

#include "mm/sys.hpp"
#include "mm/ast.hpp"
#include "smm/ast.hpp"

namespace mdl { namespace mm  {

void merge();
void cut();

namespace {

void do_parse() {
	Sys::timer()["read"].start();
	if (!parse(Lex::toInt(Sys::conf().in.name)))
		throw Error("parsing of " + Sys::conf().in.name + " failed");
	//cout << endl << *source;
	Sys::timer()["read"].stop();
}

void do_translate() {
	if (Sys::conf().out.name.empty()) throw Error("output file is not specified");
	Sys::timer()["work"].start();
	uint lab = Lex::getInt(Sys::conf().in.name);
	smm::Source* target = translate(Sys::get().math.sources.access(lab));
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
}

}

void run() {
	Sys::timer()["total"].start();
	if (Sys::conf().verbose)
		cout << "processing file " << Sys::conf().in.name << " ... " << flush;
	if (Sys::conf().mode == Mode::TRANSL) do_parse();
	//cout << *source << endl;
	switch (Sys::conf().mode) {
	case Mode::CUT:    cut();       break;
	case Mode::MERGE:  merge();     break;
	case Mode::TRANSL: do_translate(); break;
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

Sys::Sys() {
	action["read"] =
		[](const Args& args) {
			string name = args[0];
			Sys::timer()["read"].start();
			if (!parse(Lex::toInt(Sys::conf().in.name)))
				throw Error("parsing of " + name + " failed");
			//cout << endl << *source;
			Sys::timer()["read"].stop();
			return Return("success", true);
		};
}

}} // mdl::mm

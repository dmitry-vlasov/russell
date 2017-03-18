#include "mm/sys.hpp"
#include "smm/sys.hpp"

namespace mdl { namespace mm  {

void merge();
void cut();
void parse(uint src);
void translate(uint src, uint tgt);

string Math::info() const {
	string stats;
	stats += "Size:\n";
	stats += "\taxioms:     " + to_string(axioms.size()) + "\n";
	stats += "\ttheorems:   " + to_string(theorems.size()) + "\n";
	stats += "\tessentials: " + to_string(essentials.size()) + "\n";
	stats += "\tfloatings:  " + to_string(floatings.size()) + "\n";
	stats += "\n";
	return stats;
}

string Math::show() const {
	return info();
}

void write(uint tgt) {
	Sys::timer()["write"].start();
	const smm::Source* target = smm::Sys::get().math.sources.access(tgt);
	if (Sys::conf().deep) {
		deep_write(
			target,
			[](const smm::Source* src) -> const vector<smm::Node>& { return src->contents; },
			[](smm::Node n) -> smm::Source* { return n.val.inc->source; },
			[](smm::Node n) -> bool { return n.type == smm::Node::INCLUSION; }
		);
	} else {
		shallow_write(target);
	}
	Sys::timer()["write"].stop();
}

string info() {
	string stats;
	stats += Sys::get().timers.show();
	stats += "\n\n";
	stats += Sys::get().math.show();
	stats += "\n";
	return stats;
}

string show() {
	return info();
}

Sys::Sys() {
	action["read"]   = wrap_action([](const Args& args) { parse(Lex::getInt(args[0])); return Return(); }, 1);
	action["transl"] = wrap_action([](const Args& args) { translate(Lex::getInt(args[0]), Lex::getInt(args[1])); return Return(); }, 2);
	action["write"]  = wrap_action([](const Args& args) { write(Lex::getInt(args[0])); return Return(); }, 1);
	action["info"]   = wrap_action([](const Args&) { info(); return Return(); }, 0);
	action["show"]   = wrap_action([](const Args&) { show(); return Return(); }, 0);
}

void run() {
	Sys::timer()["total"].start();
	uint src = Lex::toInt(Sys::conf().in.name);
	uint tgt = Lex::toInt(Sys::conf().out.name);
	if (Sys::conf().verbose)
		cout << "processing file " << Sys::conf().in.name << " ... " << flush;
	if (Sys::conf().mode == Mode::TRANSL)
		parse(src);
	//cout << *source << endl;
	switch (Sys::conf().mode) {
	case Mode::CUT:    cut();              break;
	case Mode::MERGE:  merge();            break;
	case Mode::TRANSL: translate(src, tgt); break;
	default : break;
	}
	if (Sys::conf().mode == Mode::TRANSL)
		write(tgt);
	Sys::timer()["total"].stop();
	if (Sys::conf().verbose)
		cout << "done in " << Sys::timer()["total"] << endl;
	if (Sys::conf().info)
		cout << info() << endl;
}

}} // mdl::mm

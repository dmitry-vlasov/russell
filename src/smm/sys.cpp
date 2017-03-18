#include "smm/ast.hpp"
#include "rus/sys.hpp"
#include "mm/ast.hpp"

namespace mdl { namespace smm {

void verify();
void parse(uint);
void translate_to_rus(uint src, uint tgt);
void translate_to_mm(uint src, uint tgt);

Math::~Math() { sources.destroy(); }

string Math::info() const {
	string stats;
	stats += "Size:\n";
	stats += "\tconstants:  " + to_string(constants.size()) + "\n";
	stats += "\tassertions: " + to_string(assertions.size()) + "\n";
	return stats;
}

string Math::show() const {
	return info();
}

void translate(uint src, uint tgt) {
	if (Sys::conf().verbose)
		cout << "translating file " << Lex::toStr(src) << " ... " << flush;
	Sys::timer()["translate"].start();
	switch (Sys::conf().target) {
	case Lang::MM:  translate_to_mm(src, tgt);  break;
	case Lang::RUS: translate_to_rus(src, tgt); break;
	}
	Sys::timer()["translate"].stop();
	if (Sys::conf().verbose)
		cout << "done in " << Sys::timer()["translate"] << endl;
}

void write(uint tgt) {
	if (Sys::conf().verbose)
		cout << "writing file " << Lex::toStr(tgt) << " ... " << flush;
	Sys::timer()["write"].start();
	uint lab = Lex::toInt(Sys::conf().in.name);
	switch (Sys::conf().target) {
	case Lang::NONE: break;
	case Lang::MM: {
		const mm::Source* target = mm::Sys::get().math.sources.access(tgt);
		if (Sys::conf().deep) {
			deep_write(
				target,
				[](const mm::Source* src) -> const vector<mm::Node>& { return src->block->contents; },
				[](mm::Node n) -> mm::Source* { return n.val.inc->source; },
				[](mm::Node n) -> bool { return n.type == mm::Node::INCLUSION; }
			);
		} else {
			shallow_write(target);
		}
	}	break;
	case Lang::RUS: {
		const rus::Source* target = rus::Sys::get().math.sources.at(tgt);
		if (Sys::conf().deep) {
			deep_write(
				target,
				[](const rus::Source* src) -> const vector<rus::Node>& { return src->theory->nodes; },
				[](rus::Node n) -> rus::Source* { return n.val.imp->source; },
				[](rus::Node n) -> bool { return n.kind == rus::Node::IMPORT; }
			);
		} else {
			shallow_write(target);
		}
	}	break;
	}
	Sys::timer()["write"].stop();
	if (Sys::conf().verbose)
		cout << "done in " << Sys::timer()["write"] << endl;
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
	action["verify"] = wrap_action([](const Args&) { verify(); return Return(); }, 0);
	action["transl"] = wrap_action([](const Args& args) { translate(Lex::getInt(args[0]), Lex::getInt(args[1])); return Return(); }, 2);
	action["write"]  = wrap_action([](const Args& args) { write(Lex::getInt(args[0])); return Return(); }, 1);
	action["info"]   = wrap_action([](const Args&) { info(); return Return(); }, 0);
	action["show"]   = wrap_action([](const Args&) { info(); return Return(); }, 0);
}

void run() {
	Sys::timer()["total"].start();
	uint src = Lex::toInt(Sys::conf().in.name);
	uint tgt = Lex::toInt(Sys::conf().out.name);

	if (Sys::conf().verbose)
		cout << "processing file " << Sys::conf().in.name << " ... " << endl;

	parse(src);
	verify();
	translate(src, tgt);
	write(tgt);

	Sys::timer()["total"].stop();
	if (Sys::conf().verbose)
		cout << "all done in " << Sys::timer()["total"] << endl;
	if (Sys::conf().info)
		cout << info() << endl;
}

}} // mdl::smm

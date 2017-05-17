#include "smm/ast.hpp"
#include "rus/ast.hpp"
#include "mm/ast.hpp"

namespace mdl { namespace smm {

void verify();
void parse(uint);
void translate_to_rus(uint src, uint tgt);
void translate_to_mm(uint src, uint tgt);

template<> Table<Source>& Math::get<Source>() { return sources; }
template<> Table<Assertion>& Math::get<Assertion>() { return assertions; }
template<> const Table<Source>& Math::get<Source>() const { return sources; }
template<> const Table<Assertion>& Math::get<Assertion>() const { return assertions; }

template Table<Source>& Math::get<Source>();
template Table<Assertion>& Math::get<Assertion>();
template const Table<Source>& Math::get<Source>() const;
template const Table<Assertion>& Math::get<Assertion>() const;

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

void translate(uint src, uint tgt, Lang lang) {
	switch (lang) {
	case Lang::MM:  translate_to_mm(src, tgt);  break;
	case Lang::RUS: translate_to_rus(src, tgt); break;
	}
}

void write(uint s, bool deep) {
	if (const Source* src = Sys::get().math.get<Source>().access(s)) {
		if (deep) {
			deep_write(
				src,
				[](const Source* src) -> const vector<Node>& { return src->contents; },
				[](Node n) -> Source* { return n.val.inc->source; },
				[](Node n) -> bool { return n.type == Node::INCLUSION; }
			);
		} else {
			shallow_write(src);
		}
	} else {
		throw Error("unknown source", Lex::toStr(s));
	}
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

Return options(const vector<string>& args) {
	return mdl::options(args, Sys::conf());
}

Sys::Sys(uint id) : mdl::Sys<Sys, Math>(id) {
	actions["read"]   = Action([](const Args& args) { parse(Lex::toInt(args[0])); return Return(); }, 1, "read");
	actions["verify"] = Action([](const Args& args) { verify(); return Return(); }, 0, "verify");
	actions["transl"] = Action([](const Args& args) { translate(Lex::toInt(args[1]), Lex::toInt(args[2]), chooseLang(args[0])); return Return(); }, 2, "translate");
	actions["write"]  = Action([](const Args& args) { write(Lex::toInt(args[0]), arg<bool>(args, "deep", false)); return Return(); }, 1, "write");
	actions["info"]   = Action([](const Args&) { info(); return Return(); }, 0);
	actions["show"]   = Action([](const Args&) { info(); return Return(); }, 0);
	actions["opts"]   = Action([](const Args& args) { return options(args); }, -1);
}

}} // mdl::smm

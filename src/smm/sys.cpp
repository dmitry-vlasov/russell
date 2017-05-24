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
	stats += "\tassertions: " + to_string(assertions.size()) + "\n\n";
	stats += "assertion table:\n" + assertions.show() + "\n";
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
				[](Node n) -> Source* { return n.val.inc->source.get(); },
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
	return Sys::conf().read(args);
}

static Descr description(string name) {
	static const map<string, Descr> m = {
		{"read",   Descr("read the source",      Descr::Arg("in", "file"))},
		{"clear",  Descr("clear the source",     Descr::Arg("in", "file"))},
		{"transl", Descr("translate the source", Descr::Arg("in", "file"), Descr::Arg("out", "file"), Descr::Arg("lang", "mm|rus"))},
		{"write",  Descr("write the source",     Descr::Arg("in", "file"), Descr::Arg("deep", "true|false", true, "false"))},
		{"verify", Descr("verify all theorems",  Descr::Arg("in", "file"))},
		{"info",   Descr("info about math")},
		{"show",   Descr("show entity")},
	};
	return m.count(name) ? m.at(name) : Descr();
}

const Sys::Actions& Sys::actions() {
	static Actions actions = {
		{"systems", systems()},
		{"help",   help()},
		{"curr",   current()},
		{"read",   Action([](const Args& args) { parse(Sys::make_name(args[0])); return Return(); }, description("read"))},
		{"clear",  Action([](const Args& args) { delete Sys::get().math.get<Source>().access(Sys::make_name(args[0])); return Return(); }, description("clear"))},
		{"verify", Action([](const Args& args) { verify(); return Return(); }, description("verify"))},
		{"transl", Action([](const Args& args) { translate(Sys::make_name(args[0]), Sys::make_name(args[1]), chooseLang(args[2])); return Return(); }, description("transl"))},
		{"write",  Action([](const Args& args) { write(Sys::make_name(args[0]), args[1] == "true"); return Return(); }, description("write"))},
		{"info",   Action([](const Args& args) { return Return(info()); }, description("info"))},
		{"show",   Action([](const Args& args) { return Return(show()); }, description("show"))},
		{"opts",   Action([](const Args& args) { conf().read(args); return Return(); }, conf().descr())}
	};
	return actions;
}

}} // mdl::smm

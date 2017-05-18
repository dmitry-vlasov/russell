#include "mm/ast.hpp"
#include "smm/ast.hpp"

namespace mdl { namespace mm  {

void merge(uint src, uint tgt, uint tgt_root);
void cut(uint src, uint tgt, uint tgt_root);
void parse(uint src);
void translate(uint src, uint tgt);

Math::~Math() { sources.destroy(); }

template<> Table<Theorem>& Math::get<Theorem>() { return theorems; }
template<> Table<Axiom>& Math::get<Axiom>() { return axioms; }
template<> Table<Essential>& Math::get<Essential>() { return essentials; }
template<> Table<Source>& Math::get<Source>() { return sources; }
template<> Table<Floating>& Math::get<Floating>() { return floatings; }
template<> const Table<Theorem>& Math::get<Theorem>() const { return theorems; }
template<> const Table<Axiom>& Math::get<Axiom>() const { return axioms; }
template<> const Table<Essential>& Math::get<Essential>() const { return essentials; }
template<> const Table<Source>& Math::get<Source>() const { return sources; }
template<> const Table<Floating>& Math::get<Floating>() const { return floatings; }

template Table<Source>& Math::get<Source>();
template Table<Floating>& Math::get<Floating>();
template Table<Theorem>& Math::get<Theorem>();
template Table<Axiom>& Math::get<Axiom>();
template Table<Essential>& Math::get<Essential>();
template const Table<Theorem>& Math::get<Theorem>() const;
template const Table<Axiom>& Math::get<Axiom>() const;
template const Table<Essential>& Math::get<Essential>() const;
template const Table<Floating>& Math::get<Floating>() const;
template const Table<Source>& Math::get<Source>() const;

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

void write(uint s, bool deep) {
	if (const Source* src = Sys::get().math.get<Source>().access(s)) {
		if (deep) {
			deep_write(
				src,
				[](const Source* src) -> const vector<Node>& { return src->block->contents; },
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
		{"transl", Descr("translate the source", Descr::Arg("in", "file"), Descr::Arg("out", "file"))},
		{"write",  Descr("write the source",     Descr::Arg("in", "file"), Descr::Arg("deep", "true|false", true, "false"))},
		{"info",   Descr("info about math")},
		{"show",   Descr("show entity")},
		{"cut",    Descr("cut the source",       Descr::Arg("in", "file"), Descr::Arg("out", "file"), Descr::Arg("out-root", "dir"))},
		{"merge",  Descr("merge the source",     Descr::Arg("in", "file"), Descr::Arg("out", "file"), Descr::Arg("out-root", "dir"))}
	};
	return m.count(name) ? m.at(name) : Descr();
}

Sys::Sys(uint id) : mdl::Sys<Sys, Math>(id) {
	actions["read"]   = Action([](const Args& args) { parse(Path::make_name(args[0])); return Return(); }, description("read"));
	actions["transl"] = Action([](const Args& args) { translate(Path::make_name(args[0]), Path::make_name(args[1])); return Return(); }, description("transl"));
	actions["write"]  = Action([](const Args& args) { write(Path::make_name(args[0]), args[1] == "true"); return Return(); }, description("write"));
	actions["info"]   = Action([](const Args& args) { info(); return Return(); }, description("info"));
	actions["show"]   = Action([](const Args& args) { show(); return Return(); }, description("show"));
	actions["opts"]   = Action([](const Args& args) { Sys::conf().read(args); return Return(); }, Sys::conf().descr());
	actions["cut"]    = Action([](const Args& args) { cut(Path::make_name(args[0]), Path::make_name(args[1]), Lex::toInt(args[2])); return Return(); }, description("cut"));
	actions["merge"]  = Action([](const Args& args) { merge(Path::make_name(args[0]), Path::make_name(args[1]), Lex::toInt(args[2])); return Return(); }, description("merge"));
}

enum class Mode { CUT, MERGE, TRANSL, NONE };

inline Mode choose(const string& s) {
	if (s == "cut")    return Mode::CUT;
	if (s == "transl") return Mode::TRANSL;
	if (s == "merge")  return Mode::MERGE;
	return Mode::NONE;
}

}} // mdl::mm

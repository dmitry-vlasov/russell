#include <mm2_ast.hpp>

namespace mdl { namespace mm2  {

void merge(uint src, uint tgt, uint tgt_root);
void cut(uint src, uint tgt, uint tgt_root);
void read(uint src);
void parse();
void verify();
void translate(uint src, uint tgt);
void minimize_imports(uint src);

void Math::destroy() { sources.destroy(); }

template<> Table<Assertion>& Math::get<Assertion>() { return assertions; }
template<> Table<Source>& Math::get<Source>() { return sources; }
template<> const Table<Assertion>& Math::get<Assertion>() const { return assertions; }
template<> const Table<Source>& Math::get<Source>() const { return sources; }

string Math::info() const {
	string stats;
	stats += "Size:\n";
	stats += "\tassertions:     " + to_string(assertions.size()) + "\n";
	stats += "\n";
	return stats;
}

string Math::show() const {
	return info();
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

Return lookup(uint src, uint line, uint col, string what) {
	const Tokenable* tok = Refs<Sys>::find(src, line, col);
	if (what == "def")
		return tok ? Return("definition found", tok->token.str()) : Return("definition not found", false);
	else if (what == "loc")
		return tok ? Return("location found", tok->token.locate().show()) : Return("definition not found", false);
	else
		return Return("incorrect lookup mode: " + what, false);
}

static Descr description(string name) {
	static const map<string, Descr> m = {
		{"read",     Descr("read the source",      Descr::Arg("in", "file"))},
		{"parse",    Descr("parse all unparsed sources")},
		{"clear",    Descr("clear the source",     Descr::Arg("in", "file"))},
		{"transl",   Descr("translate the source", Descr::Arg("in", "file"), Descr::Arg("out", "file"))},
		{"write",    Descr("write the source",     Descr::Arg("in", "file"), Descr::Arg("deep", "true|false", true, "false"))},
		{"verify",   Descr("verify all theorems")},
		{"info",     Descr("info about math")},
		{"show",     Descr("show entity")},
		{"cut",      Descr("cut the source",       Descr::Arg("in", "file"), Descr::Arg("out", "file"), Descr::Arg("out-root", "dir"))},
		{"merge",    Descr("merge the source",     Descr::Arg("in", "file"), Descr::Arg("out", "file"), Descr::Arg("out-root", "dir"))},
		{"lookup",   Descr("lookup a symbol def",  Descr::Arg("in", "file"), Descr::Arg("line", "row"), Descr::Arg("col", "column"), Descr::Arg("what", "loc|def"))},
		{"minimize", Descr("minimize imports",     Descr::Arg("in", "file"))},
	};
	return m.count(name) ? m.at(name) : Descr();
}

const Sys::Actions& Sys::actions() {
	static Actions actions = {
		{"systems",  systems()},
		{"help",     help()},
		{"curr",     current()},
		{"destroy",  destroy()},
		{"read",     Action([](const Args& args) { read(Sys::make_name(args[0])); return Return(); }, description("read"))},
		{"parse",    Action([](const Args& args) { parse(); return Return(); }, description("parse"))},
		{"clear",    Action([](const Args& args) { delete Sys::get().math.get<Source>().access(Sys::make_name(args[0])); return Return(); }, description("clear"))},
		{"verify",   Action([](const Args& args) { verify(); return Return(); }, description("verify"))},
		{"transl",   Action([](const Args& args) { translate(Sys::make_name(args[0]), Sys::make_name(args[1])); return Return(); }, description("transl"))},
		{"write",    Action([](const Args& args) { write<Sys>(Sys::make_name(args[0]), args[1] == "true"); return Return(); }, description("write"))},
		{"info",     Action([](const Args& args) { return Return(info()); }, description("info"))},
		{"show",     Action([](const Args& args) { return Return(show()); }, description("show"))},
		{"cut",      Action([](const Args& args) { cut(Sys::make_name(args[0]), Sys::make_name(args[1]), Lex::toInt(args[2])); return Return(); }, description("cut"))},
		{"merge",    Action([](const Args& args) { merge(Sys::make_name(args[0]), Sys::make_name(args[1]), Lex::toInt(args[2])); return Return(); }, description("merge"))},
		{"opts",     Action([](const Args& args) { conf().read(args); return Return(); }, conf().descr())},
		{"lookup",   Action([](const Args& args) { Return ret = lookup(Sys::make_name(args[0]), stoul(args[1]), stoul(args[2]), args[3]); return ret; }, description("lookup"))},
		{"minimize", Action([](const Args& args) { minimize_imports(Sys::make_name(args[0])); return Return(); }, description("minimize"))},
	};
	return actions;
}

enum class Mode { CUT, MERGE, TRANSL, NONE };

inline Mode choose(const string& s) {
	if (s == "cut")    return Mode::CUT;
	if (s == "transl") return Mode::TRANSL;
	if (s == "merge")  return Mode::MERGE;
	return Mode::NONE;
}

}} // mdl::mm2

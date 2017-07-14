#include <mm_ast.hpp>
#include <smm_ast.hpp>

namespace mdl { namespace mm  {

void merge(uint src, uint tgt, uint tgt_root);
void cut(uint src, uint tgt, uint tgt_root);
void parse(uint src);
void translate(uint src, uint tgt);

void Math::destroy() { sources.destroy(); }

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

Return lookup(uint src, uint line, uint col, string what) {
	Tokenable* tok = Refs<Sys>::find(src, line, col);
	if (what == "def")
		return tok ? Return("definition found", tok->token.str()) : Return("definition not found", false);
	else if (what == "loc")
		return tok ? Return("location found", tok->token.locate().show()) : Return("definition not found", false);
	else
		return Return("incorrect lookup mode: " + what, false);
}

static Descr description(string name) {
	static const map<string, Descr> m = {
		{"read",   Descr("read the source",      Descr::Arg("in", "file"))},
		{"clear",  Descr("clear the source",     Descr::Arg("in", "file"))},
		{"transl", Descr("translate the source", Descr::Arg("in", "file"), Descr::Arg("out", "file"))},
		{"write",  Descr("write the source",     Descr::Arg("in", "file"), Descr::Arg("deep", "true|false", true, "false"))},
		{"info",   Descr("info about math")},
		{"show",   Descr("show entity")},
		{"cut",    Descr("cut the source",       Descr::Arg("in", "file"), Descr::Arg("out", "file"), Descr::Arg("out-root", "dir"))},
		{"merge",  Descr("merge the source",     Descr::Arg("in", "file"), Descr::Arg("out", "file"), Descr::Arg("out-root", "dir"))},
		{"lookup", Descr("lookup a symbol def",  Descr::Arg("in", "file"), Descr::Arg("line", "row"), Descr::Arg("col", "column"), Descr::Arg("what", "loc|def"))}
	};
	return m.count(name) ? m.at(name) : Descr();
}

const Sys::Actions& Sys::actions() {
	static Actions actions = {
		{"systems", systems()},
		{"help",   help()},
		{"curr",   current()},
		{"destroy", destroy()},
		{"read",   Action([](const Args& args) { parse(Sys::make_name(args[0])); return Return(); }, description("read"))},
		{"clear",  Action([](const Args& args) { delete Sys::get().math.get<Source>().access(Sys::make_name(args[0])); return Return(); }, description("clear"))},
		{"transl", Action([](const Args& args) { translate(Sys::make_name(args[0]), Sys::make_name(args[1])); return Return(); }, description("transl"))},
		{"write",  Action([](const Args& args) { write(Sys::make_name(args[0]), args[1] == "true"); return Return(); }, description("write"))},
		{"info",   Action([](const Args& args) { return Return(info()); }, description("info"))},
		{"show",   Action([](const Args& args) { return Return(show()); }, description("show"))},
		{"cut",    Action([](const Args& args) { cut(Sys::make_name(args[0]), Sys::make_name(args[1]), Lex::toInt(args[2])); return Return(); }, description("cut"))},
		{"merge",  Action([](const Args& args) { merge(Sys::make_name(args[0]), Sys::make_name(args[1]), Lex::toInt(args[2])); return Return(); }, description("merge"))},
		{"opts",   Action([](const Args& args) { conf().read(args); return Return(); }, conf().descr())},
		{"lookup", Action([](const Args& args) { Return ret = lookup(Sys::make_name(args[0]), stoul(args[1]), stoul(args[2]), args[3]); return ret; }, description("lookup"))},
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

}} // mdl::mm

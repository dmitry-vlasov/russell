#include <rus_ast.hpp>
#include <smm_ast.hpp>

namespace mdl { namespace rus {

void Math::destroy() { sources.destroy(); }

string Math::info() const {
	string stats;
	stats += "Size:\n";
	stats += "\tconstants:  " + to_string(consts.size()) + "\n";
	stats += "\ttypes:      " + to_string(types.size()) + "\n";
	stats += "\trules:      " + to_string(rules.size()) + "\n";
	stats += "\tassertions: " + to_string(assertions.size()) + "\n";
	stats += "\tproofs:     " + to_string(proofs.size()) + "\n";
	stats += "\tsources:    " + to_string(sources.size()) + "\n";
	return stats;
}

string Math::show() const {
	return info();
}

template<> Table<Const>& Math::get<Const>() { return consts; }
template<> Table<Type>& Math::get<Type>() { return types; }
template<> Table<Rule>& Math::get<Rule>() { return rules; }
template<> Table<Proof>& Math::get<Proof>() { return proofs; }
template<> Table<Source>& Math::get<Source>() { return sources; }
template<> Table<Assertion>& Math::get<Assertion>() { return assertions; }
template<> const Table<Const>& Math::get<Const>() const { return consts; }
template<> const Table<Type>& Math::get<Type>() const { return types; }
template<> const Table<Rule>& Math::get<Rule>() const { return rules; }
template<> const Table<Proof>& Math::get<Proof>() const { return proofs; }
template<> const Table<Source>& Math::get<Source>() const { return sources; }
template<> const Table<Assertion>& Math::get<Assertion>() const { return assertions; }

template Table<Const>& Math::get<Const>();
template Table<Type>& Math::get<Type>();
template Table<Rule>& Math::get<Rule>();
template Table<Proof>& Math::get<Proof>();
template Table<Source>& Math::get<Source>();
template Table<Assertion>& Math::get<Assertion>();
template const Table<Const>& Math::get<Const>() const;
template const Table<Type>& Math::get<Type>() const;
template const Table<Rule>& Math::get<Rule>() const;
template const Table<Proof>& Math::get<Proof>() const;
template const Table<Source>& Math::get<Source>() const;
template const Table<Assertion>& Math::get<Assertion>() const;

Source* parse(uint);
void verify(uint src);
void verify();
smm::Source* translate(uint src, uint tgt);

namespace {

void read(uint src) {
	rus::parse(src);
	expr::parse();
}

void parse_() {
	//expr::parse();
}

void verify_(uint src) {
	if (src == -1) rus::verify(); else rus::verify(src);
}

void translate_(uint src, uint tgt) {
	rus::translate(src, tgt);
}

void write(uint s, bool deep) {
	if (const Source* src = Sys::get().math.get<Source>().access(s)) {
		if (deep) {
			deep_write(
				src,
				[](const Source* src) -> const vector<Node>& { return src->theory->nodes; },
				[](Node n) -> Source* { return n.val.imp->source.get(); },
				[](Node n) -> bool { return n.kind == Node::IMPORT; }
			);
		} else shallow_write(src);
	} else {
		throw Error("unknown source", Lex::toStr(s));
	}
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

Return outline(uint s, uint bits) {
	const Source* src = Sys::get().math.get<Source>().access(s);
	string outline = xml_outline(*src, bits);
	return Return("source outline", outline);
}

Return structure(uint bits) {
	return Return("structure", xml_structure(bits));
}

}

string info() {
	string stats;
	stats += "Timings:";
	stats += show_timer("\n\tread:       ", "read", Sys::timer());
	stats += show_timer("\n\texpression: ", "expr", Sys::timer());
	stats += show_timer("\n\tunify:      ", "unify", Sys::timer());
	stats += show_timer("\n\ttranslate:  ", "translate", Sys::timer());
	stats += show_timer("\n\twrite:      ", "write", Sys::timer());
	stats += stats += "\n";
	stats += show_timer("\n\ttotal: ", "total", Sys::timer());
	stats += "\n\n";

	const size_t const_vol = mdl::memvol(Sys::get().math.get<Const>());
	const size_t types_vol = mdl::memvol(Sys::get().math.get<Type>());
	const size_t rules_vol = mdl::memvol(Sys::get().math.get<Rule>());
	//const size_t axiom_vol = mdl::memvol(Sys::get().math.axioms);
	//const size_t defs_vol  = mdl::memvol(Sys::get().math.defs);
	//const size_t thems_vol = mdl::memvol(Sys::get().math.theorems);
	const size_t proof_vol = mdl::memvol(Sys::get().math.get<Proof>());
	//uint lab = Lex::toInt(Sys::conf().in.name);
	const size_t source_vol = 0; //memvol(*Sys::get().math.get<Source>().access(lab));
	const size_t total_vol =
		const_vol + types_vol + rules_vol +
		//axiom_vol + defs_vol + thems_vol +
		proof_vol;

	stats += "Volume:\n";
	stats += "\tconsts:   " + showmem(const_vol) + "\n";
	stats += "\ttypes:    " + showmem(types_vol) + "\n";
	stats += "\trules:    " + showmem(rules_vol) + "\n";
	//stats += "\taxioms:   " + showmem(axiom_vol) + "\n";
	//stats += "\tdefs:     " + showmem(defs_vol) + "\n";
	//stats += "\ttheorems: " + showmem(thems_vol) + "\n";
	stats += "\tproofs:   " + showmem(proof_vol) + "\n";
	stats += "\n";
	stats += "\ttotal:  " + showmem(total_vol) + "\n";
	stats += "\tsource: " + showmem(source_vol) + "\n";
	stats += "\n";

	stats += "Size:\n";
	stats += "\tconsts:   " + to_string(Sys::get().math.get<Const>().size()) + "\n";
	stats += "\ttypes:    " + to_string(Sys::get().math.get<Type>().size()) + "\n";
	stats += "\trules:    " + to_string(Sys::get().math.get<Rule>().size()) + "\n";
	//stats += "\taxioms:   " + to_string(Sys::get().math.axioms.size()) + "\n";
	//stats += "\tdefs:     " + to_string(Sys::get().math.defs.size()) + "\n";
	//stats += "\ttheorems: " + to_string(Sys::get().math.theorems.size()) + "\n";
	stats += "\tproofs:   " + to_string(Sys::get().math.get<Proof>().size()) + "\n";
	stats += "\n";

	return stats;
}

string show() {
	return info();
}

enum class Mode { TRANSL, PROVE, NONE };

inline Mode choose(const string& s) {
	if (s == "transl") return Mode::TRANSL;
	if (s == "prove")  return Mode::PROVE;
	return Mode::NONE;
}

Return options(const Args& args) {
	return Sys::conf().read(args);
}

static Descr description(string name) {
	static map<string, Descr> m = {
		{"read",   Descr("read the source",      Descr::Arg("in", "file"))},
		{"clear",  Descr("clear the source",     Descr::Arg("in", "file"))},
		{"transl", Descr("translate the source", Descr::Arg("in", "file"), Descr::Arg("out", "file"))},
		{"write",  Descr("write the source",     Descr::Arg("in", "file"), Descr::Arg("deep", "true|false", true, "false"))},
		{"parse",  Descr("parse all expressions")},
		{"verify", Descr("verify all theorems",  Descr::Arg("in", "file", true, ""))},
		{"info",   Descr("info about math")},
		{"show",   Descr("show entity")},
		{"lookup", Descr("lookup a symbol",      Descr::Arg("in", "file"), Descr::Arg("line", "row"), Descr::Arg("col", "column"), Descr::Arg("what", "loc|def"))},
		{"outline", Descr("make an xml outline", Descr::Arg("in", "file"), Descr::Arg("what", "import,const,type,rule,axiom,def,theorem,proof,theory,problem"))},
		{"struct",  Descr("global xml structure", Descr::Arg("what", "import,const,type,rule,axiom,def,theory"))},
	};
	return m.count(name) ? m.at(name) : Descr();
}

const Sys::Actions& Sys::actions() {
	static Actions actions = {
		{"systems", systems()},
		{"help",   help()},
		{"curr",   current()},
		{"destroy", destroy()},
		{"read",   Action([](const Args& args) { read(Sys::make_name(args[0])); return Return(); }, description("read"))},
		{"clear",  Action([](const Args& args) { delete Sys::get().math.get<Source>().access(Sys::make_name(args[0])); return Return(); }, description("clear"))},
		{"parse",  Action([](const Args& args) { parse_(); return Return(); }, description("parse"))},
		{"verify", Action([](const Args& args) { verify_(Sys::make_name(args[0])); return Return(); }, description("verify"))},
		{"transl", Action([](const Args& args) { translate_(Sys::make_name(args[0]), Sys::make_name(args[1])); return Return(); }, description("transl"))},
		{"write",  Action([](const Args& args) { write(Sys::make_name(args[0]), args[1] == "true"); return Return(); }, description("write"))},
		{"info",   Action([](const Args& args) { info(); return Return(); }, description("info"))},
		{"show",   Action([](const Args& args) { info(); return Return(); }, description("show"))},
		{"opts",   Action([](const Args& args) { conf().read(args); return Return(); }, conf().descr())},
		{"lookup", Action([](const Args& args) { Return ret = lookup(Sys::make_name(args[0]), stoul(args[1]), stoul(args[2]), args[3]); return ret; }, description("lookup"))},
		{"outline", Action([](const Args& args) { Return ret = outline(Sys::make_name(args[0]), xml_bits(args[1])); return ret; }, description("outline"))},
		{"struct",  Action([](const Args& args) { Return ret = structure(xml_bits(args[0])); return ret; }, description("struct"))}
	};
	return actions;
}

}} // mdl::rus

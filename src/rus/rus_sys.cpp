#include "rus_ast.hpp"
#include "mm_ast.hpp"
#include "rus_lookup.hpp"
#include "prover/rus_prover_space.hpp"

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

void verify(uint src);
mm::Source* translate(uint src, uint tgt);
void parse_src_peg();
void parse_src_spirit();
void read(uint src);
void min_imports(uint src);
Return lookup_ref(uint src, uint line, uint col, string what);

string xml_outline(const Source&, uint);
string xml_structure(uint bits);
string xml_types();

namespace {

void parse_src() {
	if (Sys::get().config.has("peg-parser")) parse_src_peg();
	else parse_src_spirit();
}

void parse_expr() {
	expr::parse();
}

void translate_(uint src, uint tgt) {
	rus::translate(src, tgt);
}

Return outline(uint s, uint bits) {
	const Source* src = Sys::get().math.get<Source>().access(s);
	string outline = xml_outline(*src, bits);
	return Return("", outline);
}

Return structure(uint bits) {
	return Return("", xml_structure(bits));
}

Return types() {
	return Return("", xml_types());
}

Return prove(uint src, uint line, uint col, string tact) {
	Source* source = Sys::mod().math.get<Source>().access(src);
	const char* pos = locate_position(line, col, source->data().c_str());
	if (Step* step = find_obj<Step>(source, pos)) {
		return Return();
	} else if (Qed* qed = find_obj<Qed>(source, pos)) {
		prover::Tactic* tactic = prover::make_tactic(tact);
		return prover::Space::create(qed, tactic);
	} else if (Proof* proof = find_obj<Proof>(source, pos)) {
		return Return();
	}
	return Return(false);
}

Return prove_start(uint src, uint line, uint col, string mode, string tact) {
	Source* source = Sys::mod().math.get<Source>().access(src);
	const char* pos = locate_position(line, col, source->data().c_str());
	if (Step* step = find_obj<Step>(source, pos)) {
		return Return();
	} else if (Qed* qed = find_obj<Qed>(source, pos)) {
		prover::Tactic* tactic = prover::make_tactic(tact);
		if (prover::Space::create(qed, tactic)) {
			return prover::Space::get()->init();
		} else {
			return false;
		}
	} else if (Proof* proof = find_obj<Proof>(source, pos)) {
		return Return();
	}
	return Return(false);
}

Return prove_step(uint index) {
	return prover::Space::get()->expand(index);
}

Return prove_delete(uint index) {
	return prover::Space::get()->erase(index);
}

Return prove_tactic(string tact) {
	prover::Tactic* tactic = prover::make_tactic(tact);
	return Return(true);
}

Return prove_confirm(uint index) {
	return Return(true);
}

Return prove_stop() {
	return prover::Space::destroy();
}

Return prove_info(uint index, string what) {
	return prover::Space::get()->info(index, what);
}

Return prove_test(string mode) {
	if (mode == "oracle") {
		return Return(prover::test_with_oracle());
	}
	return Return();
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
		{"read",       Descr("read the source",      Descr::Arg("in", "file"))},
		{"clear",      Descr("clear the source",     Descr::Arg("in", "file"))},
		{"transl",     Descr("translate the source", Descr::Arg("in", "file"), Descr::Arg("out", "file"))},
		{"write",      Descr("write the source",     Descr::Arg("in", "file"), Descr::Arg("deep", "true|false", true, "false"))},
		{"parse",      Descr("parse all unparsed sources and expressions")},
		{"parse_src",  Descr("parse all unparsed sources")},
		{"parse_expr", Descr("parse all unparsed expressions")},
		{"verify",     Descr("verify all theorems",  Descr::Arg("in", "file", true, ""))},
		{"info",       Descr("info about math")},
		{"show",       Descr("show entity")},
		{"lookup",     Descr("lookup a symbol",      Descr::Arg("in", "file"), Descr::Arg("line", "row"), Descr::Arg("col", "column"), Descr::Arg("what", "loc|def"))},
		{"outline",    Descr("make an xml outline",  Descr::Arg("in", "file"), Descr::Arg("what", "import,const,type,rule,axiom,def,theorem,proof,theory,problem"))},
		{"struct",     Descr("global xml structure", Descr::Arg("what", "import,const,type,rule,axiom,def,theory"))},
		{"types",      Descr("type system")},
		{"prove",  Descr(
			"prove theorem automatically",
			Descr::Arg("in", "file"),
			Descr::Arg("line", "row"),
			Descr::Arg("col", "column"),
			Descr::Arg("tact", "alter({tact})|proxy[bits](tact)|breadth|oracle", true, "breadth")
		)},
		{"prove_start",  Descr(
			"start proving theorem",
			Descr::Arg("in", "file"),
			Descr::Arg("line", "row"),
			Descr::Arg("col", "column"),
			Descr::Arg("mode", "auto,inter,comb,test", true, "inter"),
			Descr::Arg("tact", "alter({tact})|proxy[bits](tact)|breadth|oracle", true, "breadth")
		)},
		{"prove_step",  Descr(
			"make a step in proving",
			Descr::Arg("index", "index")
		)},
		{"prove_delete",  Descr(
			"delete proof variant",
			Descr::Arg("index", "index")
		)},
		{"prove_tactic",  Descr(
			"switch to some tactic",
			Descr::Arg("tact", "alter({tact})|proxy[bits](tact)|breadth|oracle", true, "breadth")
		)},
		{"prove_confirm",  Descr(
			"confirm a proof",
			Descr::Arg("index", "index")
		)},
		{"prove_stop",  Descr(
			"stop proving theorem"
		)},
		{"prove_info",  Descr(
			"show an info about node",
			Descr::Arg("index", "integer"),
			Descr::Arg("what", "tree|node|children|proofs")
		)},
		{"prove_test", Descr("test prover",        Descr::Arg("mode", "oracle", true, "oracle"))},
		{"min_imports", Descr("minimize imports",  Descr::Arg("in", "file", true, ""))},
	};
	return m.count(name) ? m.at(name) : Descr();
}

const Sys::Actions& Sys::actions() {
	static Actions actions = {
		{"systems", systems()},
		{"help",       help()},
		{"curr",       current()},
		{"destroy",    destroy()},
		{"read",       Action([](const Args& args) { read(Sys::make_name(args[0])); return Return(); }, description("read"))},
		{"clear",      Action([](const Args& args) { delete Sys::get().math.get<Source>().access(Sys::make_name(args[0])); return Return(); }, description("clear"))},
		{"parse",      Action([](const Args& args) { parse_src(); parse_expr(); return Return(); }, description("parse"))},
		{"parse_src",  Action([](const Args& args) { parse_src(); return Return(); }, description("parse_src"))},
		{"parse_expr", Action([](const Args& args) { parse_expr(); return Return(); }, description("parse_expr"))},
		{"verify",     Action([](const Args& args) { verify(Sys::make_name(args[0])); return Return(); }, description("verify"))},
		{"transl",     Action([](const Args& args) { translate_(Sys::make_name(args[0]), Sys::make_name(args[1])); return Return(); }, description("transl"))},
		{"write",      Action([](const Args& args) { write<Sys>(Sys::make_name(args[0]), args[1] == "true"); return Return(); }, description("write"))},
		{"info",       Action([](const Args& args) { info(); return Return(); }, description("info"))},
		{"show",       Action([](const Args& args) { info(); return Return(); }, description("show"))},
		{"opts",       Action([](const Args& args) { conf().read(args); return Return(); }, conf().descr())},
		{"lookup",     Action([](const Args& args) { return lookup_ref(Sys::make_name(args[0]), stoul(args[1]), stoul(args[2]), args[3]); }, description("lookup"))},
		{"outline",    Action([](const Args& args) { return outline(Sys::make_name(args[0]), xml_bits(args[1])); }, description("outline"))},
		{"struct",     Action([](const Args& args) { return structure(xml_bits(args[0])); }, description("struct"))},
		{"types",      Action([](const Args& args) { return types(); }, description("types"))},

		{"prove",      Action([](const Args& args) { return prove(Sys::make_name(args[0]), stoul(args[1]), stoul(args[2]), args[3]); }, description("prove"))},

		{"prove_start",   Action([](const Args& args) { return prove_start(Sys::make_name(args[0]), stoul(args[1]), stoul(args[2]), args[3], args[4]); }, description("prove_start"))},
		{"prove_step",    Action([](const Args& args) { return prove_step(stoul(args[0])); }, description("prove_step"))},
		{"prove_delete",  Action([](const Args& args) { return prove_delete(stoul(args[0])); }, description("prove_delete"))},
		{"prove_tactic",  Action([](const Args& args) { return prove_tactic(args[0]); }, description("prove_tactic"))},
		{"prove_confirm", Action([](const Args& args) { return prove_confirm(stoul(args[0])); }, description("prove_confirm"))},
		{"prove_stop",    Action([](const Args& args) { return prove_stop(); }, description("prove_stop"))},
		{"prove_info",    Action([](const Args& args) { return prove_info(stoul(args[0]), args[1]); }, description("prove_info"))},
		{"prove_test",    Action([](const Args& args) { return prove_test(args[0]); }, description("prove_test"))},

		{"min_imports", Action([](const Args& args) { min_imports(Sys::make_name(args[0])); return Return(); }, description("min_imports"))},
	};
	return actions;
}

}} // mdl::rus

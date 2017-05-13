#include "rus/ast.hpp"
#include "smm/ast.hpp"

namespace mdl { namespace rus {

Math::~Math() { sources.destroy(); }

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
smm::Source* translate(uint src, uint tgt);

namespace {

void read(uint src) {
	if (Sys::conf().verbose) cout << "reading " << Lex::toStr(src) << " ... " << flush;
	Sys::timer()["read"].start();
	rus::parse(src);
	Sys::timer()["read"].stop();
	if (Sys::conf().verbose) cout << "done in " << Sys::timer()["read"] << endl;
}

void parse() {
	if (Sys::conf().verbose) cout << "parsing expressions ... " << flush;
	Sys::timer()["parse"].start();
	expr::parse();
	Sys::timer()["parse"].stop();
	if (Sys::conf().verbose) cout << "done in " << Sys::timer()["parse"] << endl;
}


void verify_(uint src) {
	if (Sys::conf().verbose) cout << "verifying ... " << flush;
	Sys::timer()["unify"].start();
	rus::verify(src);
	Sys::timer()["unify"].stop();
	if (Sys::conf().verbose) cout << "done in " << Sys::timer()["unify"] << endl;
}

void translate_(uint src, uint tgt) {
	if (Sys::conf().verbose) cout << "translating ... " << flush;
	Sys::timer()["translate"].start();
	rus::translate(src, tgt);
	Sys::timer()["translate"].stop();
	if (Sys::conf().verbose) cout << "done in " << Sys::timer()["translate"] << endl;
}

void write(uint tgt) {
	if (Sys::conf().verbose) cout << "writing " << Lex::toStr(tgt) << " ... " << flush;
	Sys::timer()["write"].start();
	switch (Sys::conf().target) {
	case Lang::NONE: break;
	case Lang::SMM: {
		const smm::Source* target = smm::Sys::get().math.get<smm::Source>().access(tgt);
		if (Sys::conf().deep) {
			deep_write(
				target,
				[](const smm::Source* src) -> const vector<smm::Node>& { return src->contents; },
				[](smm::Node n) -> smm::Source* { return n.val.inc->source; },
				[](smm::Node n) -> bool { return n.type == smm::Node::INCLUSION; }
			);
		} else shallow_write(target);
		break;
	}
	case Lang::RUS: {
		const Source* source = Sys::get().math.get<Source>().access(tgt);
		if (Sys::conf().deep) {
			deep_write(
				source,
				[](const Source* src) -> const vector<Node>& { return src->theory->nodes; },
				[](Node n) -> Source* { return n.val.imp->source; },
				[](Node n) -> bool { return n.kind == Node::IMPORT; }
			);
		} else shallow_write(source);
		break;
	}
	}
	Sys::timer()["write"].stop();
	if (Sys::conf().verbose) cout << "done in " << Sys::timer()["write"] << endl;
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
	uint lab = Lex::toInt(Sys::conf().in.name);
	const size_t source_vol = memvol(*Sys::get().math.get<Source>().access(lab));
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

Return options(const vector<string>& args) {
	po::variables_map vm;
	Return ret = mdl::options(args, vm);
	if (!ret) return ret;
	Conf& conf = Sys::conf();
	init_common_options(vm, conf);
	if (vm.count("translate")) {
		conf.mode = "transl";
		conf.target = Lang::SMM;
		smm::Sys::conf().in = conf.out;
		smm::Sys::conf().in.ext = "smm";
	}
	if (vm.count("prove")) {
		conf.mode = "prove";
		conf.target = Lang::RUS;
	}
	if (conf.in.name.empty()) return Return("no input file name", false);
	return Return();
}

Sys::Sys() {
	action["read"]   = wrap_action([](const Args& args) { read(Lex::getInt(args[0])); return Return(); }, 1);
	action["verify"] = wrap_action([](const Args& args) { verify_(Lex::getInt(args[0])); return Return(); }, 1);
	action["transl"] = wrap_action([](const Args& args) { translate_(Lex::getInt(args[0]), Lex::getInt(args[1])); return Return(); }, 2);
	action["write"]  = wrap_action([](const Args& args) { write(Lex::getInt(args[0])); return Return(); }, 1);
	action["info"]   = wrap_action([](const Args&) { info(); return Return(); }, 0);
	action["show"]   = wrap_action([](const Args&) { info(); return Return(); }, 0);
	action["opts"]   = wrap_action([](const Args& args) { return options(args); }, -1);
}

void run() {
	Sys::timer()["total"].start();
	uint src = Lex::toInt(Sys::conf().in.name);
	uint tgt = Lex::toInt(Sys::conf().out.name);

	if (Sys::conf().verbose)
		cout << "processing file " << Lex::toStr(src) << " ... " << endl;

	read(src);
	parse();
	verify_(src);

	switch (choose(Sys::conf().mode)) {
	case Mode::PROVE:   break;
	case Mode::TRANSL:  translate_(src, tgt); break;
	default : break;
	}

	write(tgt);

	Sys::timer()["total"].stop();
	if (Sys::conf().verbose)
		cout << "all done in " << Sys::timer()["total"] << endl;
	if (Sys::conf().opts.count("info"))
		cout << info() << endl;
}


}} // mdl::rus

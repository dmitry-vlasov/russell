#include "mm/ast.hpp"
#include "smm/ast.hpp"

namespace mdl { namespace mm  {

void merge(uint src, uint tgt, uint tgt_sys);
void cut(uint src, uint tgt, uint tgt_sys);
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

void write(uint tgt, bool deep) {
	const smm::Source* target = smm::Sys::get().math.sources.access(tgt);
	if (deep) {
		deep_write(
			target,
			[](const smm::Source* src) -> const vector<smm::Node>& { return src->contents; },
			[](smm::Node n) -> smm::Source* { return n.val.inc->source; },
			[](smm::Node n) -> bool { return n.type == smm::Node::INCLUSION; }
		);
	} else {
		shallow_write(target);
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
	actions["transl"] = Action([](const Args& args) { translate(Lex::toInt(args[0]), Lex::toInt(args[1])); return Return(); }, 2, "translate");
	actions["write"]  = Action([](const Args& args) { write(Lex::toInt(args[0]), arg<bool>(args, "deep", false)); return Return(); }, 1, "write");
	actions["info"]   = Action([](const Args&) { info(); return Return(); }, 0, "info");
	actions["show"]   = Action([](const Args&) { show(); return Return(); }, 0, "show");
	actions["opts"]   = Action([](const Args& args) { return options(args); }, -1, "options");
	actions["cut"]    = Action([](const Args& args) { cut(Lex::toInt(args[0]), Lex::toInt(args[1]), Lex::toInt(args[2])); return Return(); }, -1, "cut");
	actions["merge"]  = Action([](const Args& args) { merge(Lex::toInt(args[0]), Lex::toInt(args[1]), Lex::toInt(args[2])); return Return(); }, -1, "merge");
}

enum class Mode { CUT, MERGE, TRANSL, NONE };

inline Mode choose(const string& s) {
	if (s == "cut")    return Mode::CUT;
	if (s == "transl") return Mode::TRANSL;
	if (s == "merge")  return Mode::MERGE;
	return Mode::NONE;
}
/*
Return options(const vector<string>& args) {
	po::variables_map vm;
	Return ret = mdl::options(args, vm);
	if (!ret) return ret;
	Conf& conf = Sys::conf();
	init_common_options(vm, conf);
	if (vm.count("cut"))       conf.opts["mode"] = "cut";
	if (vm.count("merge"))     conf.opts["mode"] = "merge";
	if (vm.count("translate")) conf.opts["mode"] = "transl";
	if (!vm.count("deep")) {
		if (conf.out.ext == "smm") {
			if (conf.opts.at("mode") != "transl") return Return("translation target already chosen", false);
			conf.target = Lang::SMM;

		} else if (conf.out.ext == "mm" && conf.opts.at("mode") == "transl") {
			return Return("makes no sense traslating from a language to itself", false);
		}
		if (conf.opts.at("mode") == "cut") {
			return Return("makes no sense cutting without --deep option", false);
		}
	}
	smm::Sys::conf().in = conf.out;
	smm::Sys::conf().in.ext = "smm";
	return Return();
}

void run() {
	Sys::timer()["total"].start();
	uint src = Lex::toInt(Sys::conf().in.name);
	uint tgt = Lex::toInt(Sys::conf().out.name);
	if (Sys::conf().has_opt("verbose"))
		cout << "processing file " << Sys::conf().in.name << " ... " << flush;
	if (Sys::conf().opts.at("mode") == "transl")
		parse(src);
	//cout << *source << endl;
	switch (choose(Sys::conf().opts.at("mode"))) {
	case Mode::CUT:    cut();               break;
	case Mode::MERGE:  merge();             break;
	case Mode::TRANSL: translate(src, tgt); break;
	default : break;
	}
	if (Sys::conf().opts.at("mode") == "transl")
		write(tgt, Sys::get().conf().has_opt("deep"));
	Sys::timer()["total"].stop();
	if (Sys::conf().has_opt("verbose"))
		cout << "done in " << Sys::timer()["total"] << endl;
	if (Sys::conf().opts.count("info"))
		cout << info() << endl;
}
*/
}} // mdl::mm

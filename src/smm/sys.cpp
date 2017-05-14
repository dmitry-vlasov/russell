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

void write(uint tgt, bool deep) {
	if (Sys::conf().verbose)
		cout << "writing file " << Lex::toStr(tgt) << " ... " << flush;
	Sys::timer()["write"].start();
	switch (Sys::conf().target) {
	case Lang::NONE: break;
	case Lang::MM: {
		const mm::Source* target = mm::Sys::get().math.get<mm::Source>().access(tgt);
		if (deep) {
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
		const rus::Source* target = rus::Sys::get().math.get<rus::Source>().access(tgt);
		if (deep) {
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

Return options(const vector<string>& args) {
	po::variables_map vm;
	Return ret = mdl::options(args, vm);
	if (!ret) return ret;
	Conf& conf = Sys::conf();
	init_common_options(vm, conf);
	conf.target = chooseTgtLang(vm);
	if (!vm.count("deep") && conf.target == Lang::NONE) {
		if (conf.out.ext == "mm") conf.target = Lang::MM;
		if (conf.out.ext == "rus") conf.target = Lang::RUS;
	}
	switch (conf.target) {
	case Lang::MM :
		mm::Sys::conf().in = conf.out;
		mm::Sys::conf().in.ext = "mm";
		break;
	case Lang::RUS :
		rus::Sys::conf().in = conf.out;
		rus::Sys::conf().in.ext = "rus";
		break;
	}
	if (conf.in.name.empty()) return Return("no input file name", false);
	return Return();
}

Sys::Sys() {
	action["read"]   = wrap_action([](const Args& args) { parse(Lex::getInt(args[0])); return Return(); }, 1);
	action["verify"] = wrap_action([](const Args&) { verify(); return Return(); }, 0);
	action["transl"] = wrap_action([](const Args& args) { translate(Lex::getInt(args[0]), Lex::getInt(args[1])); return Return(); }, 2);
	action["write"]  = wrap_action([](const Args& args) { write(Lex::getInt(args[0]), arg<bool>(args, "deep", false)); return Return(); }, 1);
	action["info"]   = wrap_action([](const Args&) { info(); return Return(); }, 0);
	action["show"]   = wrap_action([](const Args&) { info(); return Return(); }, 0);
	action["opts"]   = wrap_action([](const Args& args) { return options(args); }, -1);
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
	write(tgt, Sys::get().conf().has_opt("deep"));

	Sys::timer()["total"].stop();
	if (Sys::conf().verbose)
		cout << "all done in " << Sys::timer()["total"] << endl;
	if (Sys::conf().opts.count("info"))
		cout << info() << endl;
}

}} // mdl::smm

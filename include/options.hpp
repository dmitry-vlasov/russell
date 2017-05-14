#pragma once

#include "std.hpp"
#include "conf.hpp"
#include "actions.hpp"

namespace mdl {

inline po::options_description init_option_descr() {
	po::options_description descr(
		string("Russell language implementation - mdl\n") +
		"Version: " + VERSION + "\n" +
		"Usage: mdl [options]\n"
	);
	descr.add_options()
		("help,h",      "print help message")
		("in,i",     po::value<string>(), "input file")
		("out,o",    po::value<string>(), "output file")
		("root-in",  po::value<string>(), "input root directory (for inclusions)")
		("root-out", po::value<string>(), "output root directory (for inclusions)")
		("opt",      po::value<string>(), "option in the form: opt_name=opt_value")
		("deep",        "deep translation")
		("verbose,v",   "not be silent")
		("info",        "info about math: timings, memory, stats")
		("lang-tgt", po::value<string>(), "target language: rus, mm or smm")
		("lang-src", po::value<string>(), "source language: rus, mm or smm")
		("translate,t", "translate to target language")
		("prove,p",     "prove as a Russell source")
		("cut",         "cut source into pieces")
		("merge",       "merge source from pieces")
		("daemon,d",    "start a Russell daemon")
		("console,c",   "start a Russell console")
	;
	return descr;
}

inline void init_common_options(const po::variables_map& vm, Conf& conf) {
	if (vm.count("in"))       conf.in.name_ext(vm["in"].as<string>());
	if (vm.count("out"))      conf.out.name_ext(vm["out"].as<string>());
	if (vm.count("root-in"))  conf.in.root  = vm["root-in"].as<string>();
	if (vm.count("root-out")) conf.out.root = vm["root-out"].as<string>();
	if (vm.count("verbose"))  conf.verbose = true;
	if (vm.count("deep"))     if (!conf.opts.count("deep")) conf.opts["deep"];
	if (vm.count("info"))     if (!conf.opts.count("info")) conf.opts["info"];
	if (vm.count("opt")) {
		string opt = vm["opt"].as<string>();
		int i = opt.find_last_of("=");
		string name = opt.substr(0, i);
		string value = (i == string::npos) ? "" : opt.substr(i + 1);
		conf.opts[name] = value;
	}
}

inline Lang chooseLang(const string& lang) {
	if (lang == "rus") return Lang::RUS;
	if (lang == "smm") return Lang::SMM;
	if (lang == "mm")  return Lang::MM;
	return Lang::NONE;
}

inline Lang chooseSrcLang(const po::variables_map& vm) {
	return vm.count("lang-src") ? chooseLang(vm["lang-src"].as<string>()) : Lang::NONE;
}

inline Lang chooseTgtLang(const po::variables_map& vm) {
	return vm.count("lang-tgt") ? chooseLang(vm["lang-tgt"].as<string>()) : Lang::NONE;
}

inline void convert_to_argv(const vector<string>& args, const char* argv[]) {
	for (auto& s : args) *(argv ++) = s.c_str();
}

template<class T> T arg(const Args& args, const string& name, T def);


template<>
inline bool arg<bool>(const Args& args, const string& name, bool def) {
	for (auto& arg : args) if (arg == name) return true;
	return false;
}

inline Return options(int argc, const char* argv[], po::variables_map& vm) {
	static po::options_description descr = init_option_descr();
	try {
		po::store(po::parse_command_line(argc, argv, descr), vm);
		po::notify(vm);
	} catch (std::exception& ex) {
		ostringstream os;
		os << descr;
		return Return(os.str(), false);
	}
	if (vm.count("help") || argc <= 1) {
		ostringstream os;
		os << descr;
		return Return(os.str());
	}
	return Return();
}

inline Return options(const vector<string>& args, po::variables_map& vm) {
	const int argc = args.size();
	const char* argv[argc];
	convert_to_argv(args, argv);
	return options(argc, argv, vm);
}

}

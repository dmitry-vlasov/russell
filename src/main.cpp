#include "rus/sys.hpp"
#include "smm/sys.hpp"
#include "mm/sys.hpp"

namespace po = boost::program_options;

using namespace mdl;

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

static void initConf(const boost::program_options::variables_map& vm, Conf& conf) {
	if (vm.count("in"))       conf.in.name_ext(vm["in"].as<string>());
	if (vm.count("out"))      conf.out.name_ext(vm["out"].as<string>());
	if (vm.count("root-in"))  conf.in.root  = vm["root-in"].as<string>();
	if (vm.count("root-out")) conf.out.root = vm["root-out"].as<string>();
	if (vm.count("verbose")) conf.verbose = true;
	if (vm.count("deep"))    conf.deep = true;
	if (vm.count("info"))    conf.info = true;
	if (vm.count("help"))    conf.help = true;
}

static void initOptions(boost::program_options::options_description& desc) {
	namespace po = boost::program_options;
	desc.add_options()
		("help,h",      "print help message")
		("in,i", po::value<string>(),   "input file")
		("out,o", po::value<string>(),  "output file")
		("root-in", po::value<string>(), "input root directory (for inclusions)")
		("root-out", po::value<string>(), "output root directory (for inclusions)")
		("deep,d",      "deep translation")
		("verbose,v",   "not be silent")
		("info",        "info about math: timings, memory, stats")
		("lang-tgt", po::value<string>(), "target language: rus, mm or smm")
		("lang-src", po::value<string>(), "source language: rus, mm or smm")
		("translate,t", "translate to target language")
		("prove,p",     "prove as a Russell source")
		("cut,c",       "cut source into pieces")
		("merge,m",     "merge source from pieces")
	;
}

static bool rusConf(const po::variables_map& vm) {
	Conf& conf = rus::Sys::conf();
	initConf(vm, conf);
	if (vm.count("translate")) {
		conf.mode = Mode::TRANSL;
		conf.target = Lang::SMM;
		smm::Sys::conf().in = conf.out;
		smm::Sys::conf().in.ext = "smm";
	}
	if (vm.count("prove")) {
		conf.mode = Mode::PROVE;
		conf.target = Lang::RUS;
	}
	if (conf.in.name.empty()) return false;
	return true;
}

static bool mmConf(const po::variables_map& vm) {
	Conf& conf = mm::Sys::conf();
	initConf(vm, conf);
	if (vm.count("cut"))       conf.mode = Mode::CUT;
	if (vm.count("merge"))     conf.mode = Mode::MERGE;
	if (vm.count("translate")) conf.mode = Mode::TRANSL;
	if (!conf.deep) {
		if (conf.out.ext == "smm") {
			if (conf.mode != Mode::TRANSL) return false;
			conf.target = Lang::SMM;

		} else if (conf.out.ext == "mm" && conf.mode == Mode::TRANSL) {
			return false;
		}
		if (conf.mode == Mode::CUT) {
			cout << "makes no sense cutting without --deep option" << endl;
			return false;
		}
	}
	smm::Sys::conf().in = conf.out;
	smm::Sys::conf().in.ext = "smm";
	return true;
}


static bool smmConf(const po::variables_map& vm) {
	Conf& conf = smm::Sys::conf();
	initConf(vm, conf);
	conf.target = chooseTgtLang(vm);
	if (!conf.deep && conf.target == Lang::NONE) {
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
	if (conf.in.name.empty()) return false;
	return true;
}

int main (int argc, const char* argv[])
{
	try {
		po::options_description desc(
			string("Russell language implementation - mdl\n") +
			"Version: " + VERSION + "\n" +
			"Usage: mdl [options]\n"
		);
		initOptions(desc);
		po::variables_map vm;
        po::store(po::parse_command_line(argc, argv, desc), vm);
        po::notify(vm);

        if (vm.count("help") || argc <= 1 || !vm.count("in")) {
            cout << desc << endl;
            return 0;
        }
        rus::Sys::init<>();
        smm::Sys::init<>();
        mm::Sys::init<>();

        Lang lang = chooseSrcLang(vm);
        bool success = true;
        switch (lang) {
        case Lang::RUS : success = rusConf(vm); break;
        case Lang::SMM : success = smmConf(vm); break;
        case Lang::MM  : success = mmConf(vm);  break;
        case Lang::NONE: cout << desc << endl; return 1;
        }
		if (!success) {
			cout << desc << endl;
            return 1;
		}
		switch (lang) {
        case Lang::RUS : rus::run(); break;
        case Lang::SMM : smm::run(); break;
        case Lang::MM  : mm::run();  break;
        case Lang::NONE: cout << desc << endl; return 1;
        }
	} catch (const Error& err) {
		cerr << err.what();
		return 1;
	} catch (std::exception& ex) {
		cerr << ex.what();
		return 1;
	} catch (...) {
		cerr << "unhandled exception. Sorry.\n";
		return 1;
	}
	return 0;
}

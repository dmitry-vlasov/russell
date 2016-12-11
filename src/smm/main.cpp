#include <boost/program_options.hpp>

#include "smm/globals.hpp"

namespace po = boost::program_options;

using namespace mdl;
using namespace smm;

static bool initConf(const po::variables_map& vm, Config& conf) {
	if (vm.count("in"))   conf.in = vm["in"].as<string>();
	if (vm.count("out"))  conf.out = vm["out"].as<string>();
	if (vm.count("root")) conf.root = vm["root"].as<string>();
	if (vm.count("lang")) {
		if (vm["lang"].as<string>() == "rus") {
			if (conf.target != Config::TARGET_NONE) return false;
			conf.target = Config::TARGET_RUS;
		}
		if (vm["lang"].as<string>() == "mm")  {
			if (conf.target != Config::TARGET_NONE) return false;
			conf.target = Config::TARGET_MM;
		}
	}
	if (vm.count("verbose")) conf.verbose = true;
	if (vm.count("deep"))    conf.deep = true;
	if (vm.count("info"))    conf.info = true;
	if (!conf.deep) {
		if (boost::ends_with(conf.out, ".mm"))  conf.target = Config::TARGET_MM;
		if (boost::ends_with(conf.out, ".rus")) conf.target = Config::TARGET_RUS;
	}
	if (conf.in == "") return false;
	return true;
}

int main (int argc, const char* argv[])
{
	try {
		po::options_description desc(
			string("smm verifier for simplified Metatmath\n") +
			"Version: " + VERSION + "\n" +
			"Usage: mdl [options]\n"
		);
		desc.add_options()
			("in,i",   po::value<string>(), "input file")
			("out,o",  po::value<string>(), "output file")
			("root,r", po::value<string>(), "root directory (for inclusions)")
			("lang,l", po::value<string>(), "target language: rus for Russell or mm for Metamath")
			("deep,d",      "deep translation")
			("verbose,v",   "not be silent")
			("info",        "info about math: timings, memory, stats")
			("help,h",      "print help message")
		;
		po::variables_map vm;
        po::store(po::parse_command_line(argc, argv, desc), vm);
        po::notify(vm);

        if (vm.count("help") || argc <= 1) {
            cout << desc << endl;
            return 0;
        }
        Smm& smm = Smm::mod();
        Config& conf = smm.config;
        if (!initConf(vm, conf)) {
        	cout << desc << endl;
            return 1;
        }

		smm.run();
		if (conf.verbose || smm.failed)
			cout << smm.status;
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

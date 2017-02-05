#include <boost/program_options.hpp>

#include "rus/globals.hpp"

namespace po = boost::program_options;

using namespace mdl;

static bool initConf(const po::variables_map& vm, rus::Config& conf) {
	if (vm.count("in"))   conf.in = vm["in"].as<string>();
	if (vm.count("out"))  conf.out = vm["out"].as<string>();
	if (vm.count("root")) conf.root = vm["root"].as<string>();
	if (vm.count("translate")) {
		conf.mode = rus::Config::Mode::TRANSL;
		conf.target = rus::Config::Target::SMM;
	}
	if (vm.count("prove")) {
		conf.mode = rus::Config::Mode::PROVE;
		conf.target = rus::Config::Target::RUS;
	}
	if (vm.count("verbose")) conf.verbose = true;
	if (vm.count("deep"))    conf.deep = true;
	if (vm.count("info"))    conf.info = true;
	if (conf.in == "") return false;
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
		desc.add_options()
			("help,h",      "print help message")
			("in,i", po::value<string>(),   "input file")
			("out,o", po::value<string>(),  "output file")
			("root,r", po::value<string>(), "root directory (for inclusions)")
			("translate,t", "translate to simplified Metamath (smm)")
			("prove,p",     "prove as a Russell source")
			("deep,d",      "deep translation")
			("verbose,v",   "not be silent")
			("info",        "info about math: timings, memory, stats")
		;
		po::variables_map vm;
        po::store(po::parse_command_line(argc, argv, desc), vm);
        po::notify(vm);

        if (vm.count("help") || argc <= 1 || !vm.count("in")) {
            cout << desc << endl;
            return 0;
        }
        rus::System& rus = rus::System::mod();
		rus::Config& conf = rus.config;
		if (!initConf(vm, conf)) {
			cout << desc << endl;
            return 1;
		}
		rus.run();
		if (rus.error.size()) cerr << rus.error;
		else if (conf.info)   cout << show(rus);
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

#include <boost/program_options.hpp>

#include "mm/globals.hpp"

namespace po = boost::program_options;

using namespace mdl;

static bool initConf(const po::variables_map& vm, mm::Config& conf) {
	if (vm.count("in"))        conf.in = vm["in"].as<string>();
	if (vm.count("out"))       conf.out = vm["out"].as<string>();
	if (vm.count("root"))      conf.root = vm["root"].as<string>();
	if (vm.count("verbose"))   conf.verbose = true;
	if (vm.count("deep"))      conf.deep = true;
	if (vm.count("info"))      conf.info = true;
	if (vm.count("cut"))       conf.mode = mm::Config::Mode::CUT;
	if (vm.count("merge"))     conf.mode = mm::Config::Mode::MERGE;
	if (vm.count("translate")) conf.mode = mm::Config::Mode::TRANSL;
	if (!conf.deep) {
		if (boost::ends_with(conf.out, ".smm") &&
			conf.mode != mm::Config::Mode::TRANSL) {
			return false;
		} else if (boost::ends_with(conf.out, ".mm") &&
			conf.mode == mm::Config::Mode::TRANSL) {
			return false;
		}
		if (conf.mode == mm::Config::Mode::CUT) {
			cout << "makes no sense cutting without --deep option" << endl;
			return false;
		}
	}
	return true;
}

int main (int argc, const char* argv[])
{
	try {
		po::options_description desc(
			string("mm translator from Metatmath to smm\n") +
			"Version: " + VERSION + "\n" +
			"Usage: mdl [options]\n"
		);
		desc.add_options()
			("help,h",      "print help message")
			("in,i", po::value<string>(),   "input file")
			("out,o", po::value<string>(),  "output file")
			("root,r", po::value<string>(), "root directory (for inclusions)")
			("translate,t", "translate to simplified Metamath (smm)")
			("cut,c",       "cut source into pieces")
			("merge,m",     "merge source from pieces")
			("deep,d",      "deep translation")
			("verbose,v",   "not be silent")
			("info",        "info about math: timings, memory, stats")
		;
		po::variables_map vm;
        po::store(po::parse_command_line(argc, argv, desc), vm);
        po::notify(vm);

        if (vm.count("help") || argc <= 1) {
            cout << desc << endl;
            return 0;
        }
        mm::System& mm = mm::System::mod();
        if (!initConf(vm, mm.config)) {
        	cout << desc << endl;
            return 1;
        }
		mm.run();
		if (mm.error.size()) cerr << mm.error;
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

#include "smm/globals.hpp"

using namespace mdl;
using namespace smm;

static void showHelp() {
	cout << "smm verifier for simplified Metatmath" << endl;
	cout << "Version: " << VERSION << endl;
	cout << "Usage: smm [options]" << endl;
	cout << "Options:" << endl;
	cout << " -i  --in <path>    input file"  << endl;
	cout << " -o  --out <path>   output file. Type of target is determined by extension: mm or rus"  << endl;
	cout << " -r  --root <path>  root directory (for inclusions)" << endl;
	cout << " -h  --help         print the help" << endl;
	cout << " -v  --verbose      not be silent"  << endl;
	cout << "     --info         info about math: timings, memory, stats"  << endl;
}

static bool parseConfig(int argc, const char* argv[], Config& conf) {
	if (argc <= 1) {
		conf.help = true;
		return true;
	}
	for (int i = 1; i < argc; ++ i) {
		string arg = argv[i];
		if (arg == "-i" || arg == "--in") {
			if (++ i == argc)
				return false;
			else
				conf.in = argv[i];
		} else if (arg == "-o" || arg == "--out") {
			if (++ i == argc)
				return false;
			else
				conf.out = argv[i];
		} else if (arg == "-r" || arg == "--root") {
			if (++ i == argc)
				return false;
			else
				conf.root = argv[i];
		} else if (arg == "-h" || arg == "--help")
			conf.help = true;
		else if (arg == "-v" || arg == "--verbose")
			conf.verbose = true;
		else if (arg == "--info")
			conf.info = true;
		else
			return false;
	}
	if (conf.in.empty()) return false;
	if (conf.out.empty()) return true;
	if (conf.out.substr(conf.out.size() - 3) == ".mm")
		conf.target = Config::TARGET_MM;
	else if (conf.out.substr(conf.out.size() - 4) == ".rus")
		conf.target = Config::TARGET_RUS;
	else
		return false;
	return true; // pacify the compiler
}

int main (int argc, const char* argv[])
{
	Smm& smm = Smm::mod();
	Config& conf = smm.config;
	if (!parseConfig(argc, argv, conf)) {
		showHelp();
		return 1;
	}
	if (conf.help) {
		showHelp();
		return 0;
	}
	try {
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

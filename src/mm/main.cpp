#include "mm/globals.hpp"

using namespace mdl;
using namespace mm;

static void showHelp() {
	cout << "mm translator from Metatmath to smm" << endl;
	cout << "Version: " << VERSION << endl;
	cout << "Usage: mm [options]" << endl;
	cout << "Options:" << endl;
	cout << " -i  --in <path>    input file"  << endl;
	cout << " -o  --out <path>   output file"  << endl;
	cout << " -r  --root <path>  root directory (for inclusions)" << endl;
	cout << " -h  --help         print the help" << endl;
	cout << " -v  --verbose      not be silent"  << endl;
	cout << " -t  --translate    translate source to smm" << endl;
	cout << " -d  --deep         deep translation to smm" << endl;
	cout << " -c  --cut          cut source into pieces" << endl;
	cout << " -m  --merge        merge source from pieces" << endl;
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
		else if (arg == "-c" || arg == "--cut")
			conf.mode = Config::Mode::CUT;
		else if (arg == "-m" || arg == "--merge")
			conf.mode = Config::Mode::MERGE;
		else if (arg == "-t" || arg == "--translate")
			conf.mode = Config::Mode::TRANSL;
		else if (arg == "-d" || arg == "--deep")
			conf.deep = true;
		else if (arg == "--info")
			conf.info = true;
		else
			return false;
	}
	if (conf.mode == Config::Mode::NONE) return false;
	if (!conf.out.empty() && !conf.deep) {
		if (boost::ends_with(conf.out, ".smm") &&
			conf.mode != Config::Mode::TRANSL) {
			return false;
		} else if (boost::ends_with(conf.out, ".mm") &&
			conf.mode == Config::Mode::TRANSL) {
			return false;
		}
	} else
		return false;
	return true;
}

int main (int argc, const char* argv[])
{
	Mm& mm = Mm::mod();
	Config& conf = mm.config;
	if (!parseConfig(argc, argv, conf)) {
		showHelp();
		return 1;
	}
	if (conf.help) {
		showHelp();
		return 0;
	}
	try {
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

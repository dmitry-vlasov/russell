#include "rus/globals.hpp"

using namespace mdl;
using namespace rus;

static void showHelp() {
	cout << "Russell language implementation - mdl" << endl;
	cout << "Version: " << VERSION << endl;
	cout << "Usage: mdl [options]" << endl;
	cout << "Options:" << endl;
	cout << " -i  --in <path>    input file"  << endl;
	cout << " -o  --out <path>   output file"  << endl;
	cout << " -r  --root <path>  root directory (for inclusions)" << endl;
	//cout << " -t --translate     translate to simplified Metamath (smm)" << endl;
	cout << " -h  --help         print the help" << endl;
	cout << " -d  --deep         deep translation" << endl;
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
		else if (arg == "-d" || arg == "--deep")
			conf.deep = true;
		else if (arg == "--info")
			conf.info = true;
		else
			return false;
	}
	if (conf.in.empty()) return false;
	if (conf.out.empty()) return true;
	if (!conf.deep) {
		if (boost::ends_with(conf.out, ".smm")) {
			if (conf.mode == Config::Mode::NONE)
				conf.mode = Config::Mode::TRANSL;
			else
				return false;
			conf.target = Config::Target::SMM;
		} else if (boost::ends_with(conf.out, ".rus"))
			conf.target = Config::Target::RUS;
	}
	return true;
}

int main (int argc, const char* argv[])
{
	Rus& rus = Rus::mod();
	Config& conf = rus.config;
	if (!parseConfig(argc, argv, conf)) {
		showHelp();
		return 1;
	}
	if (conf.help) {
		showHelp();
		return 0;
	}
	try {
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

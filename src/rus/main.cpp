/*****************************************************************************/
/* Project name:    smm - verifier for the Simplified MetaMath language      */
/* File Name:       smm_main.cpp                                             */
/* Description:     main function for smm                                    */
/* Copyright:       (c) 2006-2010 Dmitri Vlasov                              */
/* Author:          Dmitri Yurievich Vlasov, Novosibirsk, Russia             */
/* Email:           vlasov at academ.org                                     */
/* URL:             http://mathdevlanguage.sourceforge.net                   */
/* Modified by:                                                              */
/* License:         GNU General Public License Version 3                     */
/*****************************************************************************/

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
	cout << " -h  --help         print the help" << endl;
	cout << " -v  --verbose      not be silent"  << endl;
	cout << "     --info         info about math: timings, memory, stats"  << endl;
	cout << "     --mod-gramm    modify grammar: make it LL"  << endl;
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
		else if (arg == "--mod-gramm")
			conf.mode = Config::MODE_GRAMM;
		else
			return false;
	}
	if (conf.in.empty()) return false;
	if (!conf.out.empty()) {
		if (conf.out.substr(conf.out.size() - 4) == ".smm") {
			if (conf.mode == Config::MODE_NONE) conf.mode = Config::MODE_TRANSL;
			else return false;
			conf.target = Config::TARG_SMM;
		} else if (conf.out.substr(conf.out.size() - 4) == ".rus")
			conf.target = Config::TARG_RUS;
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
		if (conf.verbose || rus.failed)
			cout << rus.status;
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

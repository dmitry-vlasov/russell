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

#include "smm/globals.hpp"

using namespace mdl;
using namespace smm;

static void showHelp() {
	cout << "smm verifier for simplified Metatmath" << endl;
	cout << "Version: " << VERSION << endl;
	cout << "Usage: smm [options] file" << endl;
	cout << "Options:" << endl;
	cout << " -h  --help     print the help" << endl;
	cout << " -v  --verbose  not be silent"  << endl;
	cout << " -l  --labels   source with labels"  << endl;
	cout << " -i  --info     info about math: timings, memory, stats"  << endl;
	cout << " -r  --root     root directory (for inclusions)" << endl;
}

static bool parseConfig(int argc, const char* argv[], Config& conf) {
	if (argc <= 1) {
		conf.help = true;
		return true;
	}
	for (int i = 1; i < argc - 1; ++ i) {
		string arg = argv[i];
		if (arg == "-h" || arg == "--help")
			conf.help = true;
		else if (arg == "-v" || arg == "--verbose")
			conf.verbose = true;
		else if (arg == "-l" || arg == "--labels")
			conf.labels = true;
		else if (arg == "-i" || arg == "--info")
			conf.info = true;
		else if (arg == "-r" || arg == "--root") {
			if (++ i == argc)
				return false;
			else
				conf.root = argv[i];
		} else
			return false;
	}
	conf.in = argv[argc - 1];
	return true;
}

int main (int argc, const char* argv[])
{
	Smm& smm = Smm::mod();
	Config& conf = smm.config;
	if (!parseConfig(argc, argv, conf)) {
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

#include <boost/program_options.hpp>

#include "rus/globals.hpp"

namespace po = boost::program_options;

using namespace std;
using namespace mdl;
using namespace rus;

int main (int argc, const char* argv[])
{
	try {
		po::options_description desc(
			string("Russell language implementation - mdl daemon\n") +
			"Version: " + VERSION + "\n" +
			"Usage: mdld [options]\n"
		);
		desc.add_options()
			("help,h", "print help message")
			("port,p", po::value<int>()->default_value(daemon::Config::DEFAULT_PORT), "set compression level")
		;
		po::variables_map vm;
        po::store(po::parse_command_line(argc, argv, desc), vm);
        po::notify(vm);

        if (vm.count("help")) {
            cout << desc << "\n";
            return 0;
        }

        if (vm.count("port")) {
        	daemon::Config::mod().port = vm["port"].as<int>();
        	cout << "port: " << daemon::Config::mod().port << endl;
        }
	}
    catch (exception& e) {
        cerr << "error: " << e.what() << "\n";
        return 1;
    }
    catch (...) {
        cerr << "Exception of unknown type!\n";
        return 2;
    }
/*
	System& rus = System::mod();
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
*/
	return 0;
}

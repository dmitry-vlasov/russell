#include <boost/program_options.hpp>

#include "daem/globals.hpp"

namespace po = boost::program_options;

using namespace std;
using namespace mdl;

static bool initConf(const po::variables_map& vm, daemon::Config& conf) {
	if (vm.count("port")) conf.port = vm["port"].as<int>();
	if (vm.count("host")) conf.host = vm["host"].as<string>();
	if (vm.count("logs")) conf.logs = vm["logs"].as<string>();
	return true;
}


int main (int argc, const char* argv[])
{
	try {
		po::options_description desc(
			string("Russell language implementation - mdld daemon\n") +
			"Version: " + VERSION + "\n" +
			"Usage: mdld [options]\n"
		);
		desc.add_options()
			("help,h", "print help message")
			("port,p", po::value<int>()->default_value(DEFAULT_DAEMON_PORT), "daemon port")
			("host", po::value<string>()->default_value(DEFAULT_DAEMON_HOST), "daemon host")
			("logs,l", po::value<string>()->default_value(DEFAULT_DAEMON_LOGS), "log file")
		;
		po::variables_map vm;
		po::store(po::parse_command_line(argc, argv, desc), vm);
		po::notify(vm);

		if (vm.count("help") || argc <= 1) {
            cout << desc << endl;
            return 0;
        }
        daemon::Daemon& d = daemon::Daemon::mod();
        daemon::Config& conf = d.config;
        if (!initConf(vm, conf)) {
        	cout << desc << endl;
            return 1;
        }
        d.run();
	} catch (const Error& err) {
		cerr << err.what();
		return 1;
	} catch (exception& ex) {
		cerr << "error: " << ex.what() << "\n";
		return 1;
	} catch (...) {
		cerr << "Exception of unknown type!\n";
		return 2;
	}
	return 0;
}

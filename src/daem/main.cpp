#include <boost/program_options.hpp>

#include "daem/globals.hpp"

namespace po = boost::program_options;

using namespace std;
using namespace mdl;

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
			("port,p", po::value<int>()->default_value(daemon::Config::DEFAULT_PORT), "set compression level")
			("logs,l", po::value<string>()->default_value(DEFAULT_DAEMON_LOGS), "log file")
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

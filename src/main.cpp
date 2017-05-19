#include "rus/sys.hpp"
#include "smm/sys.hpp"
#include "mm/sys.hpp"
#include "daem/sys.hpp"

using namespace mdl;

int main (int argc, const char* argv[])
{
	try {
		po::options_description descr(
			string("Russell language implementation - mdl\n") +
			"Version: " + VERSION + "\n" +
			"Usage: mdl [options] | \"command_1\" ... \"command_n\" \n"
		);
		descr.add_options()
			("help,h",      "print help message")
			("daemon,d",    "start a Russell daemon")
			("console,c",   "start a Russell console")
		;
		po::variables_map vm;
		po::store(po::parse_command_line(argc, argv, descr), vm);
		po::notify(vm);
		if (vm.count("help") || argc == 1) return 0;
		if (vm.count("daemon"))  { daemon::Daemon::get(); return 0; }
		if (vm.count("console")) { daemon::Console::get(); return 0; }
		for (int i = 1; i < argc; ++ i) {
			Return ret = execute(argv[i]);
			if (!ret) {
				cerr << ret.text << endl;
				return 1;
			}
		}
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

#include "rus/sys.hpp"
#include "smm/sys.hpp"
#include "mm/sys.hpp"
#include "daem/sys.hpp"

using namespace mdl;

vector<string> make_args(int argc, const char* argv[]) {
	vector<string> args(argc);
	for (int i = 0; i < argc; ++ i)	args[i] = *argv++;
	return args;
}

int main (int argc, const char* argv[])
{
	vector<string> args = make_args(argc, argv);
	try {
		po::variables_map vm;
		if (!options(argc, argv, vm)) return 1;
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

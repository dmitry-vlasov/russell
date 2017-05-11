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

		rus::Sys::init<>();
		smm::Sys::init<>();
		mm::Sys::init<>();

		if (vm.count("daemon"))  { daemon::Daemon::get(); return 0; }
		if (vm.count("console")) { daemon::Console::get(); return 0; }

		if (!vm.count("in")) { cerr << "no input file is chosen" << endl; return 1; }

		Lang lang = chooseSrcLang(vm);
		Return ret;
		switch (lang) {
		case Lang::RUS : ret = rus::Sys::mod().action["opts"](args); break;
		case Lang::SMM : ret = smm::Sys::mod().action["opts"](args); break;
		case Lang::MM  : ret = mm::Sys::mod().action["opts"](args);  break;
		case Lang::NONE: cerr << "no language is chosen" << endl; return 1;
		}
		if (!ret) { cerr << "error: " << ret.text << endl; return 1; }
		switch (lang) {
		case Lang::RUS : rus::run(); break;
		case Lang::SMM : smm::run(); break;
		case Lang::MM  : mm::run();  break;
		case Lang::NONE: cerr << "no language is chosen" << endl; return 1;
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

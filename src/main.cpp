#include "rus/sys.hpp"
#include "smm/sys.hpp"
#include "mm/sys.hpp"
#include "daem/sys.hpp"

using namespace mdl;

enum class Mode { DAEM, CONS, EXEC };

int main (int argc, const char* argv[])
{
	try {
		po::options_description descr(
			string("Russell language implementation - mdl\n") +
			"Version: " + VERSION + "\n" +
			"Usage: mdl [options] | \"command_1\" ... \"command_n\" \n"
		);
		descr.add_options()
			("help,h", "print help message")
			("daem,d", "start a Russell daemon")
			("cons,c", "start a Russell console")
		;
		po::variables_map vm;
		po::store(po::parse_command_line(argc, argv, descr), vm);
		po::notify(vm);
		Mode mode = Mode::EXEC;
		if (vm.count("help") || argc == 1) return 0;
		if (vm.count("daem")) mode = Mode::DAEM;
		if (vm.count("cons")) mode = Mode::CONS;
		for (int i = 1; i < argc; ++ i) {
			if (argv[i][0] == '-') continue;
			switch (mode) {
			case Mode::DAEM: Daemon::mod().enqueue(argv[i]);  break;
			case Mode::CONS: Console::mod().enqueue(argv[i]); break;
			case Mode::EXEC: {
					Return ret = execute(argv[i]);
					if (!ret) {
						cerr << ret.text << endl;
						return 1;
					}
				}
			};
		}
		switch (mode) {
		case Mode::DAEM: Daemon::mod().start();  break;
		case Mode::CONS: Console::mod().start(); break;
		case Mode::EXEC: break;
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

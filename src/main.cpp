#include <daem.hpp>
#include "rus_sys.hpp"
#include "mm_sys.hpp"

#ifdef BUILD_SOLID
	#include "all.cpp"
#endif

using namespace mdl;

enum class Mode { DAEM, CLI, CONS, EXEC, HELP };

int main (int argc, const char* argv[])
{
	try {
		Timer timer;
		timer.start();
		po::options_description descr(
			string("Russell language implementation - mdl\n") +
			"Version: " + RUSSELL_VERSION_MAJOR + "." + RUSSELL_VERSION_MINOR + "\n" +
			"Usage: mdl [options] | \"command_1\" ... \"command_n\" \n"
		);
		descr.add_options()
			("help,h", "print help message")
			("daem,d", "start a Russell daemon")
			("cli",    "start a Russell client")
			("cons,c", "start a Russell console")
			("verb,v", "verbose daemon/console")
			("cleanup", "release memory after execution")
		;
		po::variables_map vm;
		po::store(po::parse_command_line(argc, argv, descr), vm);
		po::notify(vm);
		Mode mode = Mode::EXEC;
		if (vm.count("help") || argc == 1) mode = Mode::HELP;
		if (vm.count("daem")) mode = Mode::DAEM;
		if (vm.count("cons")) mode = Mode::CONS;
		if (vm.count("cli"))  mode = Mode::CLI;
		bool verb = vm.count("verb");
		queue<string> commands;
		for (int i = 1; i < argc; ++ i) {
			if (argv[i][0] == '-') continue;
			switch (mode) {
			case Mode::DAEM: Daemon::mod().enqueue(argv[i]);  break;
			case Mode::CLI:  Client::mod().enqueue(argv[i]);  break;
			case Mode::CONS: Console::mod().enqueue(argv[i]); break;
			case Mode::EXEC: commands.push(argv[i]); break;
			}
		}
		switch (mode) {
		case Mode::DAEM: Daemon::mod().start(verb);  break;
		case Mode::CLI:  Client::mod().start(verb);  break;
		case Mode::CONS: Console::mod().start(verb); break;
		case Mode::EXEC: execute(commands);          break;
		case Mode::HELP: cout << descr << endl;      break;
		}
		if (vm.count("cleanup")) {
			rus::Sys::release();
			mm::Sys::release();
		}
		timer.stop();
		if (verb) {
			cout << "total execution time: " << timer << endl;
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

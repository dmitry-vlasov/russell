#include "rus/sys.hpp"
#include "smm/sys.hpp"

namespace po = boost::program_options;

using namespace mdl;

static bool initConf(const po::variables_map& vm, rus::Config& conf) {
	mdl::initConf(vm, conf);
	if (vm.count("translate")) {
		conf.mode = rus::Config::Mode::TRANSL;
		conf.target = rus::Config::Target::SMM;
		smm::System::conf().in = conf.out;
		smm::System::conf().in.ext = "smm";
	}
	if (vm.count("prove")) {
		conf.mode = rus::Config::Mode::PROVE;
		conf.target = rus::Config::Target::RUS;
	}
	if (conf.in.name.empty()) return false;
	return true;
}

int main (int argc, const char* argv[])
{
	try {
		po::options_description desc(
			string("Russell language implementation - mdl\n") +
			"Version: " + VERSION + "\n" +
			"Usage: mdl [options]\n"
		);
		mdl::initOptions(desc);
		desc.add_options()
			("translate,t", "translate to simplified Metamath (smm)")
			("prove,p",     "prove as a Russell source")
		;
		po::variables_map vm;
        po::store(po::parse_command_line(argc, argv, desc), vm);
        po::notify(vm);

        if (vm.count("help") || argc <= 1 || !vm.count("in")) {
            cout << desc << endl;
            return 0;
        }
        rus::System::init<>();
        smm::System::init<>();
		if (!initConf(vm, rus::System::conf())) {
			cout << desc << endl;
            return 1;
		}
		rus::run();
		if (rus::System::conf().info) cout << rus::info() << endl;
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

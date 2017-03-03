#include "smm/sys.hpp"

namespace po = boost::program_options;

using namespace mdl;

static bool initConf(const po::variables_map& vm, smm::Config& conf) {
	mdl::initConf(vm, conf);
	if (vm.count("lang")) {
		if (vm["lang"].as<string>() == "rus") {
			if (conf.target != smm::Config::Target::TARGET_NONE) return false;
			conf.target = smm::Config::Target::TARGET_RUS;
		}
		if (vm["lang"].as<string>() == "mm")  {
			if (conf.target != smm::Config::Target::TARGET_NONE) return false;
			conf.target = smm::Config::Target::TARGET_MM;
		}
	}
	if (!conf.deep && conf.target == smm::Config::Target::TARGET_NONE) {
		if (conf.out.ext == "mm") conf.target = smm::Config::Target::TARGET_MM;
		if (conf.out.ext == "rus") conf.target = smm::Config::Target::TARGET_RUS;
	}
	if (conf.in.name.empty()) return false;
	return true;
}

int main (int argc, const char* argv[])
{
	try {
		po::options_description desc(
			string("smm verifier for simplified Metatmath\n") +
			"Version: " + VERSION + "\n" +
			"Usage: mdl [options]\n"

		);
		mdl::initOptions(desc);
		desc.add_options()
			("lang,l", po::value<string>(), "target language: rus for Russell or mm for Metamath")
		;
		po::variables_map vm;
        po::store(po::parse_command_line(argc, argv, desc), vm);
        po::notify(vm);

        if (vm.count("help") || argc <= 1) {
            cout << desc << endl;
            return 0;
        }
        smm::System& sys = smm::System::mod();
        smm::Config& conf = sys.config;
        if (!initConf(vm, conf)) {
        	cout << desc << endl;
            return 1;
        }
		smm::run(sys);
		if (sys.error.size()) cerr << sys.error;
		if (conf.info) cout << info(sys);
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

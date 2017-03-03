#include "mm/sys.hpp"

namespace po = boost::program_options;

using namespace mdl;

static bool initConf(const po::variables_map& vm, mm::Config& conf) {
	mdl::initConf(vm, conf);
	if (vm.count("cut"))       conf.mode = mm::Config::Mode::CUT;
	if (vm.count("merge"))     conf.mode = mm::Config::Mode::MERGE;
	if (vm.count("translate")) conf.mode = mm::Config::Mode::TRANSL;
	if (!conf.deep) {
		if (conf.out.ext == "smm") {
			if (conf.mode != mm::Config::Mode::TRANSL) return false;
			conf.target = mm::Config::Target::SMM;

		} else if (conf.out.ext == "mm" && conf.mode == mm::Config::Mode::TRANSL) {
			return false;
		}
		if (conf.mode == mm::Config::Mode::CUT) {
			cout << "makes no sense cutting without --deep option" << endl;
			return false;
		}
	}
	return true;
}

int main (int argc, const char* argv[])
{
	try {
		po::options_description desc(
			string("mm translator from Metatmath to smm\n") +
			"Version: " + VERSION + "\n" +
			"Usage: mdl [options]\n"
		);
		mdl::initOptions(desc);
		desc.add_options()
			("translate,t", "translate to simplified Metamath (smm)")
			("cut,c",       "cut source into pieces")
			("merge,m",     "merge source from pieces")
		;
		po::variables_map vm;
        po::store(po::parse_command_line(argc, argv, desc), vm);
        po::notify(vm);

        if (vm.count("help") || argc <= 1) {
            cout << desc << endl;
            return 0;
        }
        mm::System& sys = mm::System::mod();
        mm::Config& conf = sys.config;
        if (!initConf(vm, conf)) {
        	cout << desc << endl;
            return 1;
        }
		mm::run(sys);
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

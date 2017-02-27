#include <boost/filesystem.hpp>
#include "smm/globals.hpp"

namespace mdl { namespace smm {

static bool parse(System& sys) {
	try {
		sys.timers["read"].start();
		sys.source = smm::parse(sys.config.in);
		//cout << *sys.source << endl;
		sys.timers["read"].stop();
		return true;
	} catch (Error& err) {
		sys.error += '\n';
		sys.error += err.what();
		return false;
	}
}

static bool verify(System& sys) {
	try {
		sys.timers["verify"].start();
		smm::verify();
		sys.timers["verify"].stop();
		return true;
	} catch (Error& err) {
		sys.error += '\n';
		sys.error += err.what();
		return false;
	}
}

static bool translate(System& sys) {
	try {
		if (sys.config.out.empty()) return true;
		if (sys.config.verbose)
			cout << "translating file " << sys.config.in << " ... " << flush;
		sys.timers["translate"].start();
		switch (sys.config.target) {
		case Config::Target::TARGET_NONE: break;
		case Config::Target::TARGET_MM: {
			mm::Source* target = smm::translate_to_mm(sys.source);
			if (sys.config.deep) {
				deep_write(
					target,
					[](mm::Source* src) -> vector<mm::Node>& { return src->block->contents; },
					[](mm::Node n) -> mm::Source* { return n.val.inc->source; },
					[](mm::Node n) -> bool { return n.type == mm::Node::INCLUSION; }
				);
			} else {
				ofstream out(sys.config.out);
				out << *target << endl;
				out.close();
			}
			delete target;
		}	break;
		case Config::Target::TARGET_RUS: {
			rus::Source* target = smm::translate_to_rus(sys.source);
			if (sys.config.deep) {
				deep_write(
					target,
					[](rus::Source* src) -> vector<rus::Node>& { return src->theory->nodes; },
					[](rus::Node n) -> rus::Source* { return n.val.imp->source; },
					[](rus::Node n) -> bool { return n.kind == rus::Node::IMPORT; }
				);
			} else {
				ofstream out(sys.config.out);
				out << *target << endl;
				out.close();
			}
			delete target;
		}	break;
		}
		sys.timers["translate"].stop();
		if (sys.config.verbose)
			cout << "done in " << sys.timers["translate"] << endl;
		return true;
	} catch (Error& err) {
		sys.error += '\n';
		sys.error += err.what();
		return false;
	}
}

void run(System& sys) {
	sys.timers["total"].start();
	if (sys.config.verbose)
		cout << "verifying file " << sys.config.in << " ... " << endl;
	if (!parse(sys))     return;
	if (!verify(sys))    return;
	if (!translate(sys)) return;
	sys.timers["total"].stop();
	if (sys.config.verbose)
		cout << "all done in " << sys.timers["total"] << endl;
}

string show(const System& sys) {
	return info(sys);
}

string info(const System& sys) {
	string stats;
	if (sys.error.size()) stats += "error:\n" + sys.error + "\n\n";
	stats += "Timings:";
	stats += show_timer("\n\tread:      ", "read", sys.timers);
	stats += show_timer("\n\tverify:    ", "verify", sys.timers);
	stats += show_timer("\n\ttranslate: ", "translate", sys.timers);
	stats += show_timer("\n\ttotal:     ", "total", sys.timers);
	stats += "\n\n";
	stats += "Size:\n";
	stats += "\tconstants:  " + to_string(sys.math.constants.size()) + "\n";
	stats += "\tassertions: " + to_string(sys.math.assertions.size()) + "\n";
	stats += "\n";
	return stats;
}

	
}} // mdl::smm

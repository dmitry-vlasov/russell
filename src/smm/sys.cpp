#include <boost/filesystem.hpp>

#include "smm/sys.hpp"

namespace mdl { namespace smm {

static bool parse(System& sys) {
	try {
		sys.timers["read"].start();
		uint lab = Lex::toInt(sys.config.in.name);
		Source* src = smm::parse(sys.config.in.path());
		//cout << *sys.source << endl;
		sys.math.sources[lab] = src;
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
		if (sys.config.out.name.empty()) return true;
		if (sys.config.verbose)
			cout << "translating file " << sys.config.in.name << " ... " << flush;
		sys.timers["translate"].start();
		uint lab = Lex::toInt(sys.config.in.name);
		switch (sys.config.target) {
		case Config::Target::TARGET_NONE: break;
		case Config::Target::TARGET_MM: {
			mm::Source* target = smm::translate_to_mm(sys.math.sources[lab]);
			if (sys.config.deep) {
				deep_write(
					target,
					[](mm::Source* src) -> vector<mm::Node>& { return src->block->contents; },
					[](mm::Node n) -> mm::Source* { return n.val.inc->source; },
					[](mm::Node n) -> bool { return n.type == mm::Node::INCLUSION; }
				);
			} else {
				//shallow_write(target);
				ofstream out(sys.config.out.path());
				out << *target << endl;
				out.close();
			}
			delete target;
		}	break;
		case Config::Target::TARGET_RUS: {
			rus::Source* target = smm::translate_to_rus(sys.math.sources[lab]);
			if (sys.config.deep) {
				deep_write(
					target,
					[](rus::Source* src) -> vector<rus::Node>& { return src->theory->nodes; },
					[](rus::Node n) -> rus::Source* { return n.val.imp->source; },
					[](rus::Node n) -> bool { return n.kind == rus::Node::IMPORT; }
				);
			} else {
				//shallow_write(target);
				ofstream out(sys.config.out.path());
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
		cout << "verifying file " << sys.config.in.name << " ... " << endl;
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

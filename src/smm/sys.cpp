#include <boost/filesystem.hpp>

#include "smm/sys.hpp"

namespace mdl { namespace smm {

static bool do_parse() {
	try {
		Sys::timer()["read"].start();
		parse(Sys::conf().in);
		Sys::timer()["read"].stop();
		return true;
	} catch (Error& err) {
		Sys::io().err() << err.what() << endl;
		return false;
	}
}

static bool do_verify() {
	try {
		Sys::timer()["verify"].start();
		smm::verify();
		Sys::timer()["verify"].stop();
		return true;
	} catch (Error& err) {
		Sys::io().err() << err.what() << endl;
		return false;
	}
}

static bool do_translate() {
	try {
		if (Sys::conf().out.name.empty()) return true;
		if (Sys::conf().verbose)
			cout << "translating file " << Sys::conf().in.name << " ... " << flush;
		Sys::timer()["translate"].start();
		uint lab = Lex::toInt(Sys::conf().in.name);
		switch (Sys::conf().target) {
		case Lang::NONE: break;
		case Lang::MM: {
			mm::Source* target = smm::translate_to_mm(Sys::get().math.sources.at(lab));
			if (Sys::conf().deep) {
				deep_write(
					target,
					[](mm::Source* src) -> vector<mm::Node>& { return src->block->contents; },
					[](mm::Node n) -> mm::Source* { return n.val.inc->source; },
					[](mm::Node n) -> bool { return n.type == mm::Node::INCLUSION; }
				);
			} else {
				//shallow_write(target);
				ofstream out(Sys::conf().out.path());
				out << *target << endl;
				out.close();
			}
		}	break;
		case Lang::RUS: {
			rus::Source* target = smm::translate_to_rus(Sys::get().math.sources.at(lab));
			if (Sys::conf().deep) {
				deep_write(
					target,
					[](rus::Source* src) -> vector<rus::Node>& { return src->theory->nodes; },
					[](rus::Node n) -> rus::Source* { return n.val.imp->source; },
					[](rus::Node n) -> bool { return n.kind == rus::Node::IMPORT; }
				);
			} else {
				shallow_write(target);
			}
		}	break;
		}
		Sys::timer()["translate"].stop();
		if (Sys::conf().verbose)
			cout << "done in " << Sys::timer()["translate"] << endl;
		return true;
	} catch (Error& err) {
		Sys::io().err() << err.what() << endl;
		return false;
	}
}

void run() {
	Sys::timer()["total"].start();
	if (Sys::conf().verbose)
		cout << "verifying file " << Sys::conf().in.name << " ... " << endl;
	if (!do_parse())     return;
	if (!do_verify())    return;
	if (!do_translate()) return;
	Sys::timer()["total"].stop();
	if (Sys::conf().verbose)
		cout << "all done in " << Sys::timer()["total"] << endl;
}

string show() {
	return info();
}

string info() {
	string stats;
	stats += "Timings:";
	stats += show_timer("\n\tread:      ", "read", Sys::timer());
	stats += show_timer("\n\tverify:    ", "verify", Sys::timer());
	stats += show_timer("\n\ttranslate: ", "translate", Sys::timer());
	stats += show_timer("\n\ttotal:     ", "total", Sys::timer());
	stats += "\n\n";
	stats += "Size:\n";
	stats += "\tconstants:  " + to_string(Sys::get().math.constants.size()) + "\n";
	stats += "\tassertions: " + to_string(Sys::get().math.assertions.size()) + "\n";
	stats += "\n";
	return stats;
}

Sys::Sys() {
}
	
}} // mdl::smm

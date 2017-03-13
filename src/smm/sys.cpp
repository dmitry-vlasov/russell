#include <boost/filesystem.hpp>

#include "smm/sys.hpp"

namespace mdl { namespace smm {

//System::System(const string& n) {
//	name = n;
//}

static bool do_parse() {
	try {
		System::timer()["read"].start();
		parse(System::conf().in);
		System::timer()["read"].stop();
		return true;
	} catch (Error& err) {
		System::io().err() << err.what() << endl;
		return false;
	}
}

static bool do_verify() {
	try {
		System::timer()["verify"].start();
		smm::verify();
		System::timer()["verify"].stop();
		return true;
	} catch (Error& err) {
		System::io().err() << err.what() << endl;
		return false;
	}
}

static bool do_translate() {
	try {
		if (System::conf().out.name.empty()) return true;
		if (System::conf().verbose)
			cout << "translating file " << System::conf().in.name << " ... " << flush;
		System::timer()["translate"].start();
		uint lab = Lex::toInt(System::conf().in.name);
		switch (System::conf().target) {
		case Config::Target::TARGET_NONE: break;
		case Config::Target::TARGET_MM: {
			mm::Source* target = smm::translate_to_mm(System::get().math.sources.at(lab));
			if (System::conf().deep) {
				deep_write(
					target,
					[](mm::Source* src) -> vector<mm::Node>& { return src->block->contents; },
					[](mm::Node n) -> mm::Source* { return n.val.inc->source; },
					[](mm::Node n) -> bool { return n.type == mm::Node::INCLUSION; }
				);
			} else {
				//shallow_write(target);
				ofstream out(System::conf().out.path());
				out << *target << endl;
				out.close();
			}
		}	break;
		case Config::Target::TARGET_RUS: {
			rus::Source* target = smm::translate_to_rus(System::get().math.sources.at(lab));
			if (System::conf().deep) {
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
		System::timer()["translate"].stop();
		if (System::conf().verbose)
			cout << "done in " << System::timer()["translate"] << endl;
		return true;
	} catch (Error& err) {
		System::io().err() << err.what() << endl;
		return false;
	}
}

void run() {
	System::timer()["total"].start();
	if (System::conf().verbose)
		cout << "verifying file " << System::conf().in.name << " ... " << endl;
	if (!do_parse())     return;
	if (!do_verify())    return;
	if (!do_translate()) return;
	System::timer()["total"].stop();
	if (System::conf().verbose)
		cout << "all done in " << System::timer()["total"] << endl;
}

string show() {
	return info();
}

string info() {
	string stats;
	stats += "Timings:";
	stats += show_timer("\n\tread:      ", "read", System::timer());
	stats += show_timer("\n\tverify:    ", "verify", System::timer());
	stats += show_timer("\n\ttranslate: ", "translate", System::timer());
	stats += show_timer("\n\ttotal:     ", "total", System::timer());
	stats += "\n\n";
	stats += "Size:\n";
	stats += "\tconstants:  " + to_string(System::get().math.constants.size()) + "\n";
	stats += "\tassertions: " + to_string(System::get().math.assertions.size()) + "\n";
	stats += "\n";
	return stats;
}

	
}} // mdl::smm

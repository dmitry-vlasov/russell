#include <boost/filesystem.hpp>
#include "smm/globals.hpp"

namespace mdl {

string show_sy(Symbol symb) {
	return smm::System::get().lex.symbols.toStr(symb.lit);
}
string show_id(uint lab) {
	return smm::System::get().lex.labels.toStr(lab);
}

namespace smm {

void System::run() {
	timers.total.start();
	if (config.verbose)
		cout << "verifying file " << config.in << " ... " << endl;
	if (!parse()) {
		failed = true; return;
	}
	if (!verify()) {
		failed = true; return;
	}
	if (!translate()) {
		failed = true; return;
	}
	timers.total.stop();
	if (config.verbose)
		cout << "all done in " << timers.total << endl;
}

bool System::parse() {
	try {
		timers.read.start();
		source = smm::parse(config.in);
		//cout << *source << endl;
		timers.read.stop();
		return true;
	} catch (Error& err) {
		status += '\n';
		status += err.what();
		failed = true;
		return false;
	}
}

bool System::verify() {
	try {
		timers.verify.start();
		smm::verify(math.assertions);
		timers.verify.stop();
		return true;
	} catch (Error& err) {
		status += '\n';
		status += err.what();
		failed = true;
		return false;
	}
}

bool System::translate() {
	try {
		if (config.out.empty()) return true;
		if (config.verbose)
			cout << "translating file " << config.in << " ... " << flush;
		timers.translate.start();
		switch (config.target) {
		case Config::Target::TARGET_NONE: break;
		case Config::Target::TARGET_MM: {
			mm::Source* target = smm::translate_to_mm(source);
			if (config.deep) {
				deep_write(
					target,
					[](mm::Source* src) -> vector<mm::Node>& { return src->block->contents; },
					[](mm::Node n) -> mm::Source* { return n.val.inc->source; },
					[](mm::Node n) -> bool { return n.type == mm::Node::INCLUSION; }
				);
			} else {
				ofstream out(config.out);
				out << *target << endl;
				out.close();
			}
			delete target;
		}	break;
		case Config::Target::TARGET_RUS: {
			rus::Source* target = smm::translate_to_rus(source);
			if (config.deep) {
				deep_write(
					target,
					[](rus::Source* src) -> vector<rus::Node>& { return src->theory->nodes; },
					[](rus::Node n) -> rus::Source* { return n.val.imp->source; },
					[](rus::Node n) -> bool { return n.kind == rus::Node::IMPORT; }
				);
			} else {
				ofstream out(config.out);
				out << *target << endl;
				out.close();
			}
			delete target;
		}	break;
		}
		timers.translate.stop();
		if (config.verbose)
			cout << "done in " << timers.translate << endl;
		return true;
	} catch (Error& err) {
		status += '\n';
		status += err.what();
		failed = true;
		return false;
	}
}

ostream& operator << (ostream& os, const System& s) {
	os << s.status;
	return os;
}
	
}} // mdl::smm

#include <boost/filesystem.hpp>
#include "smm/globals.hpp"

namespace mdl {

string show_sy(Symbol symb) {
	return smm::Smm::get().lex.symbols.toStr(symb.lit);
}
string show_id(uint lab) {
	return smm::Smm::get().lex.labels.toStr(lab);
}

namespace smm {

void Smm::run() {
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

bool Smm::parse() {
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

bool Smm::verify() {
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

namespace fs = boost::filesystem;

namespace {
	vector<mm::Node>& get_mm_cont(mm::Source* src) { return src->block->contents; }
	mm::Source* get_mm_inc(mm::Node n) { return n.val.inc->source; }
	bool is_mm_inc(mm::Node n) { return n.type == mm::Node::INCLUSION; }

	vector<rus::Node>& get_rus_cont(rus::Source* src) { return src->theory->nodes; }
	rus::Source* get_rus_inc(rus::Node n) { return n.val.imp->source; }
	bool is_rus_inc(rus::Node n) { return n.kind == rus::Node::IMPORT; }
}

bool Smm::translate() {
	try {
		if (config.out.empty()) return true;
		if (config.verbose)
			cout << "translating file " << config.in << " ... " << flush;
		timers.translate.start();
		switch (config.target) {
		case Config::TARGET_NONE: break;
		case Config::TARGET_MM: {
			mm::Source* target = smm::translate_to_mm(source);
			if (config.deep) {
				deep_write(target, get_mm_cont, get_mm_inc, is_mm_inc);
			} else {
				ofstream out(config.out);
				out << *target << endl;
				out.close();
			}
			delete target;
		}	break;
		case Config::TARGET_RUS: {
			rus::Source* target = smm::translate_to_rus(source);
			if (config.deep) {
				deep_write(target, get_rus_cont, get_rus_inc, is_rus_inc);
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

ostream& operator << (ostream& os, const Smm& s) {
	os << s.status;
	return os;
}
	
}} // mdl::smm

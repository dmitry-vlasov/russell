#include <boost/filesystem.hpp>

#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "cut/ast.hpp"
#include "merge/ast.hpp"
#include "mm/globals.hpp"

namespace mdl {

string show_sy(Symbol symb) {
	return mm::Mm::get().lex.symbols.toStr(symb.lit);
}
string show_id(uint lab) {
	return mm::Mm::get().lex.labels.toStr(lab);
}

namespace mm { namespace {

bool parse_mm(Mm& mm) {
	try {
		mm.timers.read.start();
		mm.source = parse(mm.config.in);
		//cout << endl << *source;
		mm.timers.read.stop();
		return true;
	} catch (Error& err) {
		mm.error += '\n';
		mm.error += err.what();
		return false;
	}
}

bool cut_mm(Mm& mm) {
	try {
		mm.timers.work.start();
		cut::Section* source = cut::parse(mm.config.root, mm.config.in, mm.config.out);
		cut::split(source);
		cut::save(source);
		delete source;
		mm.timers.work.stop();
		return true;
	} catch (Error& err) {
		mm.error += '\n';
		mm.error += err.what();
		return false;
	}
}

bool merge_mm(Mm& mm) {
	try {
		mm.timers.work.start();
		merge::parse(mm.config.in);
		ofstream out(mm.config.out);
		out << merge::Source::get().contents.str();
		out.close();
		mm.timers.work.stop();
		return true;
	} catch (Error& err) {
		mm.error += '\n';
		mm.error += err.what();
		return false;
	}
}

namespace fs = boost::filesystem;

namespace {
	vector<smm::Node>& get_cont(smm::Source* src) { return src->contents; }
	smm::Source* get_inc(smm::Node n) { return n.val.inc->source; }
	bool is_inc(smm::Node n) { return n.type == smm::Node::INCLUSION; }
}

bool translate_mm(Mm& mm) {
	try {
		if (mm.config.out.empty()) {
			mm.error += "output file is not specified";
			return false;
		}
		mm.timers.work.start();
		smm::Source* target = translate(mm.source);
		if (mm.config.deep) {
			deep_write(target, get_cont, get_inc, is_inc);
		} else {
			ofstream out(mm.config.out);
			out << *target << endl;
			out.close();
		}
		delete target;
		mm.timers.work.stop();
		return true;
	} catch (Error& err) {
		mm.error += '\n';
		mm.error += err.what();
		return false;
	}
}

}

void Mm::run() {
	timers.total.start();
	if (config.verbose)
		cout << "processing file " << config.in << " ... " << flush;
	if (config.mode != Config::Mode::MERGE && !parse_mm(*this)) return;
	//cout << *source << endl;
	switch (config.mode) {
	case Config::Mode::CUT:    cut_mm(*this);       break;
	case Config::Mode::MERGE:  merge_mm(*this);     break;
	case Config::Mode::TRANSL: translate_mm(*this); break;
	default : break;
	}
	timers.total.stop();
	if (config.verbose)
		cout << "done in " << timers.total << endl;
}
	
}} // mdl::mm

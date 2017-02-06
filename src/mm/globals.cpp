#include <boost/filesystem.hpp>

#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "cut/ast.hpp"
#include "merge/ast.hpp"
#include "mm/globals.hpp"

namespace mdl {

string show_sy(Symbol symb) {
	return mm::System::get().lex.symbols.toStr(symb.lit);
}
string show_id(uint lab) {
	return mm::System::get().lex.labels.toStr(lab);
}

namespace mm {

Source* parse_spirit(string path);
Source* parse_peg(string path);

Source* parse(string path) {
	return parse_peg(path);
}

namespace {

bool parse_mm(System& mm) {
	try {
		mm.timers["read"].start();
		mm.source = parse(mm.config.in);
		if (!mm.source) throw Error("parsing of " + mm.config.in + " failed");
		//cout << endl << *source;
		mm.timers["read"].stop();
		return true;
	} catch (Error& err) {
		mm.error += '\n';
		mm.error += err.what();
		return false;
	}
}

bool cut_mm(System& mm) {
	try {
		mm.timers["work"].start();
		cut::Section* source = cut::parse(mm.config.root, mm.config.in, mm.config.out);
		cut::split(source);
		cut::save(source);
		delete source;
		mm.timers["work"].stop();
		return true;
	} catch (Error& err) {
		mm.error += '\n';
		mm.error += err.what();
		return false;
	}
}

bool merge_mm(System& mm) {
	try {
		mm.timers["work"].start();
		merge::parse(mm.config.in);
		ofstream out(mm.config.out);
		out << merge::Source::get().contents.str();
		out.close();
		mm.timers["work"].stop();
		return true;
	} catch (Error& err) {
		mm.error += '\n';
		mm.error += err.what();
		return false;
	}
}

bool translate_mm(System& mm) {
	try {
		if (mm.config.out.empty()) {
			mm.error += "output file is not specified";
			return false;
		}
		mm.timers["work"].start();
		smm::Source* target = translate(mm.source);
		if (mm.config.deep) {
			deep_write(
				target,
				[](smm::Source* src) -> vector<smm::Node>& { return src->contents; },
				[](smm::Node n) -> smm::Source* { return n.val.inc->source; },
				[](smm::Node n) -> bool { return n.type == smm::Node::INCLUSION; }
			);
		} else {
			ofstream out(mm.config.out);
			out << *target << endl;
			out.close();
		}
		delete target;
		mm.timers["work"].stop();
		return true;
	} catch (Error& err) {
		mm.error += '\n';
		mm.error += err.what();
		return false;
	}
}

}

void run(System& sys) {
	sys.timers["total"].start();
	if (sys.config.verbose)
		cout << "processing file " << sys.config.in << " ... " << flush;
	if (sys.config.mode == Config::Mode::TRANSL)
		if (!parse_mm(sys))
			return;
	//cout << *source << endl;
	switch (sys.config.mode) {
	case Config::Mode::CUT:    cut_mm(sys);       break;
	case Config::Mode::MERGE:  merge_mm(sys);     break;
	case Config::Mode::TRANSL: translate_mm(sys); break;
	default : break;
	}
	sys.timers["total"].stop();
	if (sys.config.verbose)
		cout << "done in " << sys.timers["total"] << endl;
}

string show(const System& rus) {
	return info(rus);
}

string info(const System& sys) {
	string stats;
	stats += "Timings:";
	stats += show_timer("\n\tread:  ", "read", sys.timers);
	stats += show_timer("\n\twork:  ", "work", sys.timers);
	stats += show_timer("\n\ttotal: ", "total", sys.timers);
	stats += "\n\n";
	stats += "Size:\n";
	stats += "\taxioms:     " + to_string(sys.math.axioms.size()) + "\n";
	stats += "\ttheorems:   " + to_string(sys.math.theorems.size()) + "\n";
	stats += "\tessentials: " + to_string(sys.math.essentials.size()) + "\n";
	stats += "\tfloatings:  " + to_string(sys.math.floatings.size()) + "\n";
	stats += "\n";
	return stats;
}


}} // mdl::mm

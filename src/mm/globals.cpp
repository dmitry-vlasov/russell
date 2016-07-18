#include "mm/ast.hpp"
#include "smm/ast.hpp"
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

bool translate_mm(Mm& mm) {
	try {
		if (mm.config.out.empty()) {
			mm.error += "output file is not specified";
			return false;
		}
		mm.timers.translate.start();
		smm::Source* target = translate(mm.source);
		//cout << endl << *target;
		ofstream out(mm.config.out);
		out << *target << endl;
		out.close();
		delete target;
		mm.timers.translate.stop();
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
		cout << "translating file " << config.in << " ... " << flush;
	if (!parse_mm(*this)) return;
	if (!translate_mm(*this)) return;
	timers.total.stop();
	if (config.verbose)
		cout << "done in " << timers.total << endl;
}
	
}} // mdl::mm

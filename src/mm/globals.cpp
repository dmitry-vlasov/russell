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

namespace mm {

void Mm::run() {
	timers.total.start();
	if (config.verbose)
		cout << "translating file " << config.in << " ... " << flush;
	if (!parse()) return;
	if (!translate()) return;
	timers.total.stop();
	if (config.verbose)
		cout << "done in " << timers.total << endl;
}

bool Mm::parse() {
	try {
		timers.read.start();
		source = mm::parse(config.in);
		//cout << endl << *source;
		timers.read.stop();
		return true;
	} catch (Error& err) {
		error += '\n';
		error += err.what();
		return false;
	}
}

bool Mm::translate() {
	try {
		if (config.out.empty()) {
			error += "output file is not specified";
			return false;
		}
		timers.translate.start();
		smm::Source* target = mm::translate(source);
		//cout << endl << *target;
		ofstream out(config.out);
		out << *target << endl;
		out.close();
		delete target;
		timers.translate.stop();
		return true;
	} catch (Error& err) {
		error += '\n';
		error += err.what();
		return false;
	}
}
	
}} // mdl::mm

/*****************************************************************************/
/* Project name:    smm - verifier for the Simplified MetaMath language      */
/* File Name:       smm_main.cpp                                             */
/* Description:     main function for smm                                    */
/* Copyright:       (c) 2006-2010 Dmitri Vlasov                              */
/* Author:          Dmitri Yurievich Vlasov, Novosibirsk, Russia             */
/* Email:           vlasov at academ.org                                     */
/* URL:             http://mathdevlanguage.sourceforge.net                   */
/* Modified by:                                                              */
/* License:         GNU General Public License Version 3                     */
/*****************************************************************************/

#include "rus/globals.hpp"

namespace mdl {

void label::write(ostream& os) {
	os << rus::Rus::get().lex.ids.toStr(lab);
}
string label::show() {
	return rus::Rus::get().lex.ids.toStr(lab);
}
void symbol::write(ostream& os) {
	os << rus::Rus::get().lex.symbs.toStr(lit);
}
string symbol::show() {
	return rus::Rus::get().lex.symbs.toStr(lit);
}
ostream& operator << (ostream& os, Symbol symb) {
	os << rus::Rus::get().lex.symbs.toStr(symb.lit);
	return os;
}

namespace rus {

void Rus::run() {
	timers.total.start();
	if (config.verbose)
		cout << "verifying file " << config.in << " ... " << flush;
	if (!parse()) {
		failed = true; return;
	}
	if (!unify()) {
		failed = true; return;
	}
	if (!translate()) {
		failed = true; return;
	}
	timers.total.stop();
	if (config.verbose)
		cout << "done in " << timers.total << endl;
}

bool Rus::parse() {
	try {
		timers.read.start();
		source = rus::parse(config.in);
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

bool Rus::unify() {
	try {
		timers.unify.start();
		rus::unify(source);
		timers.unify.stop();
		return true;
	} catch (Error& err) {
		status += '\n';
		status += err.what();
		failed = true;
		return false;
	}
}


bool Rus::translate() {
	try {
		if (config.out.empty()) return true;
		if (config.verbose)
			cout << "translating file " << config.in << " ... " << flush;
		timers.translate.start();
		smm::Source* target = rus::translate(source);
		//cout << endl << *target;
		ofstream out(config.out);
		out << *target << endl;
		out.close();
		delete target;
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

ostream& show (ostream& os, const Rus& s) {
	os << s.status;
	return os;
}
	
}} // mdl::rus

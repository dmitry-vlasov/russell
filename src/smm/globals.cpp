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

bool Smm::translate() {
	try {
		if (config.out.empty()) return true;
		if (config.verbose)
			cout << "translating file " << config.in << " ... " << flush;
		timers.translate.start();
		switch (config.target) {
		case Config::TARGET_NONE: break;
		case Config::TARGET_MM: {
			mm::Block* target = smm::translate_to_mm(source);
			//cout << endl << *target;
			ofstream out(config.out);
			out << *target << endl;
			out.close();
			delete target;
		}	break;
		case Config::TARGET_RUS: {
			rus::Source* target = smm::translate_to_rus(source);
			//cout << endl << *target;
			ofstream out(config.out);
			out << *target << endl;
			out.close();
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

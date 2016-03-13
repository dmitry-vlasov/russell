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

#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "mm/globals.hpp"

namespace mdl {

void label::write(ostream& os) {
	os << mm::Mm::get().lex.labels.toStr(lab);
}

namespace mm {

void Mm::run() {
	timers.total.start();
	if (config.verbose)
		cout << "translating file " << config.in << " ... " << flush;
	if (!parse()) {
		failed = true; return;
	}
	if (!translate()) {
		failed = true; return;
	}
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
		status += '\n';
		status += err.what();
		failed = true;
		return false;
	}
}

bool Mm::translate() {
	try {
		if (config.out.empty()) {
			status += "output file is not specified";
			return false;
		}
		timers.translate.start();
		smm::Source* target = mm::translate(source);
		cout << endl << *target;
		ofstream out(config.out);
		out << *target << endl;
		out.close();
		delete target;
		timers.translate.stop();
		return true;
	} catch (Error& err) {
		status += '\n';
		status += err.what();
		failed = true;
		return false;
	}
}

ostream& show (ostream& os, const Mm& s) {
	os << s.status;
	return os;
}
	
}} // mdl::mm

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
#include "mm/globals.hpp"

namespace mdl { namespace mm {

void Node::destroy() {
	switch(type) {
	case NONE: break;
	case CONSTANTS:  delete val.cst; break;
	case VARIABLES:  delete val.var; break;
	case DISJOINTED: delete val.dis; break;
	case FLOATING:   delete val.flo; break;
	case ESSENTIAL:  delete val.ess; break;
	case AXIOM:      delete val.ax;  break;
	case THEOREM:    delete val.th;  break;
	case BLOCK:      delete val.blk; break;
	default : assert(false && "impossible"); break;
	}
	type = NONE;
}

Theorem::~Theorem() {
	if (proof)
		delete proof;
}

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

		cout << endl << *source;
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
		timers.translate.start();
		target = mm::translate(source);
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

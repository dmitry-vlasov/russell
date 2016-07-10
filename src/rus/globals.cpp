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

#include "rus/expr/table.hpp"
#include "rus/globals.hpp"

namespace mdl {

string show_sy(Symbol symb) {
	return rus::Rus::get().lex.symbs.toStr(symb.lit);
}
string show_id(uint lab) {
	return rus::Rus::get().lex.ids.toStr(lab);
}

namespace rus { namespace {

bool parse_rus(Rus& rus) {
	try {
		cout << "parsing russell source ... " << flush;
		rus.timers.read.start();
		rus.source = parse(rus.config.in);
		expr::parse();
		//cout << *rus.source << endl;
		rus.timers.read.stop();
		cout << "done in " << rus.timers.read << endl;
		return true;
	} catch (Error& err) {
		rus.status += '\n';
		rus.status += err.what();
		rus.failed = true;
		return false;
	}
}

bool unify_rus(Rus& rus) {
	try {
		cout << "verifying russell source ... " << flush;
		rus.timers.unify.start();
		verify(rus.source);
		rus.timers.unify.stop();
		cout << "done in " << rus.timers.unify << endl;
		return true;
	} catch (Error& err) {
		rus.status += '\n';
		rus.status += err.what();
		rus.failed = true;
		return false;
	}
}


bool translate_rus(Rus& rus) {
	try {
		if (rus.config.out.empty()) return true;
		if (rus.config.verbose)
			cout << "translating file " << rus.config.in << " ... " << flush;
		rus.timers.translate.start();
		smm::Source* target = translate(rus.source);
		//cout << endl << *target;
		ofstream out(rus.config.out);
		out << *target << endl;
		out.close();
		delete target;
		rus.timers.translate.stop();
		if (rus.config.verbose)
			cout << "done in " << rus.timers.translate << endl;
		return true;
	} catch (Error& err) {
		rus.status += '\n';
		rus.status += err.what();
		rus.failed = true;
		return false;
	}
}

bool write_rus(Rus& rus) {
	try {
		if (rus.config.out.empty()) return true;
		if (rus.config.verbose)
			cout << "replicating file " << rus.config.in << " ... " << flush;
		//cout << endl << *rus.source;
		rus.timers.translate.start();
		ofstream out(rus.config.out);
		out << *rus.source << endl;
		out.close();
		rus.timers.translate.stop();
		if (rus.config.verbose)
			cout << "done in " << rus.timers.translate << endl;
		return true;
	} catch (Error& err) {
		rus.status += '\n';
		rus.status += err.what();
		rus.failed = true;
		return false;
	}
}

}

void Rus::run() {
	timers.total.start();
	if (config.verbose)
		cout << "processing file " << config.in << " ... " << endl;
	if (!parse_rus(*this)) {
		failed = true; return;
	}
	if (config.mode != Config::MODE_GRAMM && !unify_rus(*this)) {
		failed = true; return;
	}
	switch (config.mode) {
	case Config::MODE_GRAMM:  modify_grammar(source); break;
	case Config::MODE_PROVE:  break;
	case Config::MODE_TRANSL: break;
	default : break;
	}

	//if (!unify_rus(*this)) {
	//	failed = true; return;
	//}

	switch (config.target) {
	case Config::TARG_RUS: write_rus(*this); break;
	case Config::TARG_SMM: translate_rus(*this); break;
	default : break;
	}
	timers.total.stop();
	if (config.verbose)
		cout << "all done in " << timers.total << endl;
}

ostream& operator << (ostream& os, const Rus& s) {
	os << s.status;
	return os;
}
	
}} // mdl::rus

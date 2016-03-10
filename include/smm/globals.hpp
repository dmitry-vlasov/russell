/*****************************************************************************/
/* Project name:    smm - verifier for the Simplified MetaMath language      */
/* File name:       smm_auxiliary_Volume.hpp                                 */
/* Description:     volume counters                                          */
/* Copyright:       (c) 2006-2010 Dmitri Vlasov                              */
/* Author:          Dmitri Yurievich Vlasov, Novosibirsk, Russia             */
/* Email:           vlasov at academ.org                                     */
/* URL:             http://mathdevlanguage.sourceforge.net                   */
/* Modified by:                                                              */
/* License:         GNU General Public License Version 3                     */
/*****************************************************************************/

#pragma once

#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace smm {

struct Config {
	Config() :
	labels(false), verbose(false), info(false), help(false),
	in(), root() { }

	bool labels;
	bool verbose;
	bool info;
	bool help;

	string in;
	string root;
};

struct Smm {
	~ Smm() {
		if (source)
			delete source;
	}

	struct Lex {
		Table labels;
		Table symbols;
	};
	struct Timers {
		Timer read;
		Timer verify;
		Timer total;
	};
	struct Math {
		set<Symbol>        constants;
		vector<Assertion*> assertions;
	};

	Config  config;
	Timers  timers;
	Lex     lex;
	Math    math;
	Source* source;
	string  status;
	bool    failed;

	void run();
	bool parse();
	bool verify();

	static const Smm& get() { return mod();}
	static Smm& mod() { static Smm smm; return smm; }
};

ostream& show (ostream& os, const Smm& s);
Source* parse(const string& path);
void verify(const vector<Assertion*>& theory);

}} // mdl::smm


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

#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace mm {

struct Config {
	Config() :
	verbose(false), info(false), help(false),
	in(), root() { }

	bool verbose;
	bool info;
	bool help;

	string in;
	string out;
	string root;
};

typedef smm::Source Target;

struct Mm {
	~ Mm() {
		if (source) delete source;
	}

	struct Lex {
		Table labels;
		Table symbols;
	};
	struct Timers {
		Timer read;
		Timer translate;
		Timer total;
	};
	struct Math {
		set<Symbol>      constants;
		vector<Theorem*> theorems;
		map<uint, Node*> table;
	};

	Config  config;
	Timers  timers;
	Lex     lex;
	Math    math;
	Block*  source;
	Target* target;
	string  status;
	bool    failed;

	void run();
	bool parse();
	bool translate();

	static const Smm& get() { return mod(); }
	static Smm& mod() { static Smm smm; return smm; }
};

ostream& show (ostream& os, const Mm& s);
Block* parse(const string& path);
Target* translate(const Block* source);

}} // mdl::mm


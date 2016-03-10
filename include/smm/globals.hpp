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

struct Smm : public Showable {
	~ Smm() {
		if (source) delete source;
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

	virtual void show (string&) const;

	static const Smm& get() { return mod(); }
	static Smm& mod() { static Smm smm; return smm; }
};

namespace parse {
Source* source(const string& path);
}

namespace parse1 {
Source* source(const string& path);
}

namespace verify {
void math(const vector<Assertion*>& theory);
}
namespace gen {
string expr(const mdl::Expr& ex);
string constants(const smm::Constants* consts);
string assertion(const smm::Assertion* consts);
string source(const smm::Source* consts);
}

}} // mdl::smm


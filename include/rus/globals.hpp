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

#include "rus/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace rus {

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

struct Rus {
	~ Rus() {
		if (source) delete source;
	}

	struct Lex {
		Table ids;
		Table symbs;
	};
	struct Timers {
		Timer read;
		Timer unify;
		Timer translate;
		Timer total;
	};
	template<typename T>
	struct Table {
		map<uint, T> table;
		bool has(uint lab) const {
			return table.find(lab) != table.end();
		}
		T& operator[] (uint ind) {
			return table[ind];
		}
	};
	struct Math {
		Table<Theorem*>   theorems;
		Table<Axiom*>     axioms;
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
	bool unify();
	bool translate();

	static const Rus& get() { return mod(); }
	static Rus& mod() { static Rus rus; return rus; }
};

ostream& operator << (ostream& os, const Rus& s);
Source* parse(const string& path);
void unify(Source*);
smm::Source* translate(const Source* source);

}} // mdl::rus


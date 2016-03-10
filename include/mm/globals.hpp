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
	template<typename T>
	struct Table {
		map<uint, T> table;
		bool has(uint lab) const {
			return table.find(lab) != table.end();
		}
	};
	struct Math {
		//set<Symbol>       constants;
		Table<Theorem*>   theorems;
		Table<Axiom*>     axioms;
		Table<Essential*> essentials;
		Table<Floating*>  floatings;
		vector<Theorem*>  theory;
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

	static const Mm& get() { return mod(); }
	static Mm& mod() { static Mm mm; return mm; }
};

ostream& show (ostream& os, const Mm& s);
Block* parse(const string& path);
Target* translate(const Block* source);

}} // mdl::mm


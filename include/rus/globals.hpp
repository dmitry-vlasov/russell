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
	enum Mode   { MODE_NONE, MODE_TRANSL, MODE_GRAMM, MODE_PROVE };
	enum Target { TARG_NONE, TARG_SMM, TARG_RUS };
	Config() :
	verbose(false), info(false), help(false),
	mode(MODE_NONE),
	in(), root(), target(TARG_NONE) { }

	bool verbose;
	bool info;
	bool help;

	Mode mode;

	string in;
	string out;
	string root;
	Target target;
};

struct Rus {
	~ Rus() { if (source) delete source; }

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
	using Table = Map<uint, T>;

	struct Math {
		Table<Type*>    types;
		Table<Theorem*> theorems;
		Table<Axiom*>   axioms;
		Table<Def*>     defs;
		Table<Rule*>    rules;
		Set<Symbol>     consts;
	};

	Config  config;
	Timers  timers;
	Lex     lex;
	Math    math;
	Source* source;
	string  status;
	bool    failed;

	void run();

	static const Rus& get() { return mod(); }
	static Rus& mod() { static Rus rus; return rus; }
};

ostream& operator << (ostream& os, const Rus& s);
Source* parse(const string& path);
void verify(Source*);
smm::Source* translate(const Source* source);
void modify_grammar(Source* src);

}} // mdl::rus


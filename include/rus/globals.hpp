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
	enum Mode   { MODE_NONE, MODE_TRANSL, MODE_PROVE };
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
		Timer parse_rus;
		Timer parse_expr;
		Timer unify;
		Timer translate;
		Timer total;
	};
	template<typename T>
	using Table = Map<uint, T>;

	struct Math {
		Table<Const*>   consts;
		Table<Type*>    types;
		Table<Rule*>    rules;
		Table<Axiom*>   axioms;
		Table<Def*>     defs;
		Table<Theorem*> theorems;
		Table<Proof*>   proofs;
	};

	Config  config;
	Timers  timers;
	Lex     lex;
	Math    math;
	Source* source;
	string  error;

	void run();

	static const Rus& get() { return mod(); }
	static Rus& mod() { static Rus rus; return rus; }
};

string show(const Rus&);
inline ostream& operator << (ostream& os, const Rus& r) { os << show(r); return os; }
Source* parse(const string& path);
void verify(Source*);
smm::Source* translate(const Source* source);

namespace parser {
	uint get_ind();
	uint inc_ind();
}

}} // mdl::rus


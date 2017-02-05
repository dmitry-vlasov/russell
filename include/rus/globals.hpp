#pragma once

#include "rus/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace rus {

enum class Mode { NONE, TRANSL, PROVE, MONITOR, DEFAULT = NONE };
enum class Target { NONE, SMM, RUS, DEFAULT = NONE };
typedef mdl::Config<Mode, Target> Config;

// Deductive system
struct System {
	~ System() { if (source) delete source; }

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
	using Table = map<uint, T>;

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

	static const System& get() { return mod(); }
	static System& mod() { return Lib<System>::mod().sys(); }
};

string show(const System&);
inline ostream& operator << (ostream& os, const System& r) { os << show(r); return os; }
Source* parse(string path);
void verify(Source*);
smm::Source* translate(const Source* source);

namespace parser {
	uint get_ind();
	uint inc_ind();
}

}} // mdl::rus


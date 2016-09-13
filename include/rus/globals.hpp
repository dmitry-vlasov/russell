#pragma once

#include "rus/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace rus {

struct Config {
	enum {
		DEFAULT_PORT = 808011
	};
	enum class Mode   { APP, SERVICE, DEFAULT = APP };
	enum class Task   { NONE, TRANSL, PROVE, MONITOR };
	enum class Target { NONE, SMM, RUS };
	Config() :
	verbose(false), info(false), help(false), deep(false),
	task(Task::NONE), mode(Mode::DEFAULT),
	in(), root(), target(Target::NONE), port(DEFAULT_PORT) { }

	bool verbose;
	bool info;
	bool help;
	bool deep;

	Task task;
	Mode mode;

	string in;
	string out;
	string root;
	Target target;
	uint   port;
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

	static const Rus& get() { return mod(); }
	static Rus& mod() { static Rus rus; return rus; }
};

string show(const Rus&);
inline ostream& operator << (ostream& os, const Rus& r) { os << show(r); return os; }
Source* parse(string path);
void verify(Source*);
smm::Source* translate(const Source* source);
void monitor();

namespace parser {
	uint get_ind();
	uint inc_ind();
}

}} // mdl::rus


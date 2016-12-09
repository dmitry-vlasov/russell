#pragma once

#include "rus/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace rus {

struct Config {
	enum {
		DEFAULT_PORT = 808011
	};
	enum class Mode   { NONE, TRANSL, PROVE, MONITOR };
	enum class Target { NONE, SMM, RUS };
	Config() :
	verbose(false), info(false), help(false), deep(false),
	mode(Mode::NONE),
	in(), root(), target(Target::NONE), port(DEFAULT_PORT) { }

	bool verbose;
	bool info;
	bool help;
	bool deep;

	Mode mode;

	string in;
	string out;
	string root;
	Target target;
	uint   port;
};

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
	static System& mod() { static System rus; return rus; }
};

// Library, singleton, which contains a variety of deductive systems
struct Lib {
	static const Lib& get() { return mod(); }
	static Lib& mod() { static Lib lib; return lib; }

	System& sys() { return systems[current]; }
	const System& sys() const { return systems[current]; }

	map<string, System> systems;
	string current;
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


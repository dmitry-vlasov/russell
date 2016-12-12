#pragma once

#include "rus/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace rus {

// Configuration for a deductive system
struct Config {
	enum class Mode   { NONE, TRANSL, PROVE, MONITOR };
	enum class Target { NONE, SMM, RUS };
	Config() :
	verbose(false), info(false), help(false), deep(false),
	mode(Mode::NONE),
	in(), root(), target(Target::NONE) { }

	bool verbose;
	bool info;
	bool help;
	bool deep;

	Mode mode;

	string in;
	string out;
	string root;
	Target target;
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
	static System& mod();
};

// Library, singleton, which contains a variety of deductive systems
struct Lib {
	static const Lib& get() { return mod(); }
	static Lib& mod() { static Lib lib; return lib; }

	System& sys() { return systems[current]; }

	map<string, System> systems;
	string current;

private:
	Lib() : systems(), current() { }
};

inline System& System::mod() { return Lib::mod().sys(); }

string show(const System&);
inline ostream& operator << (ostream& os, const System& r) { os << show(r); return os; }
Source* parse(string path);
void verify(Source*);
smm::Source* translate(const Source* source);

namespace daemon {

#define DEFAULT_DAEMON_LOGS "/var/tmp/mdld.log"

struct Config {
	enum {
		DEFAULT_PORT = 808011
	};
	static const Config& get() { return mod(); }
	static Config& mod() { static Config d; return d; }
	uint   port;
	string logs;

private:
	Config() : port(DEFAULT_PORT), logs(DEFAULT_DAEMON_LOGS) { }
};

}

void execute(const string& command);

namespace parser {
	uint get_ind();
	uint inc_ind();
}

}} // mdl::rus


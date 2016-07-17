#pragma once

#include "smm/ast.hpp"
#include "mm/ast.hpp"
#include "rus/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace smm {

struct Config {
	enum Target { TARGET_NONE, TARGET_MM, TARGET_RUS };
	Config() :
	verbose(false), info(false), help(false),
	in(), root(), target(TARGET_NONE) { }

	bool verbose;
	bool info;
	bool help;

	string in;
	string out;
	string root;
	Target target;
};

struct Smm {
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
		Timer translate;
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
	bool translate();

	static const Smm& get() { return mod();}
	static Smm& mod() { static Smm smm; return smm; }
};

ostream& operator << (ostream& os, const Smm& s);
Source* parse(const string& path);
void verify(const vector<Assertion*>& theory);
mm::Source*  translate_to_mm(const Source* source);
rus::Source* translate_to_rus(const Source* source);

}} // mdl::smm


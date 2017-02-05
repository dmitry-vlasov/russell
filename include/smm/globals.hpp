#pragma once

#include "smm/ast.hpp"
#include "mm/ast.hpp"
#include "rus/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace smm {

enum class Mode { TRANSL, DEFAULT = TRANSL };
enum class Target { TARGET_NONE, TARGET_MM, TARGET_RUS, DEFAULT = TARGET_NONE };
typedef mdl::Config<Mode, Target> Config;

struct System {
	~ System() {
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

	static const System& get() { return mod();}
	static System& mod() { return Lib<System>::mod().sys();  }
};

ostream& operator << (ostream& os, const System& s);
Source* parse(string path);
void verify(const vector<Assertion*>& theory);
mm::Source*  translate_to_mm(const Source* source);
rus::Source* translate_to_rus(const Source* source);

}} // mdl::smm


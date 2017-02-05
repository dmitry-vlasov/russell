#pragma once

#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace mm {

enum class Mode { NONE, TRANSL, CUT, MERGE, DEFAULT = NONE };
enum class Target { SMM, DEFAULT = SMM };
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
		Timer work;
		Timer total;
	};
	template<typename T>
	using Table = map<uint, T>;

	struct Math {
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
	Source* source;
	string  error;

	void run();

	static const System& get() { return mod(); }
	static System& mod() { return Lib<System>::mod().sys();  }
};

Source* parse_spirit(string path);
Source* parse_peg(string path);
Source* parse(string path);

smm::Source* translate(const Source* source);

}} // mdl::mm


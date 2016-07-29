#pragma once

#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace mm {

struct Config {
	enum class Mode   { NONE, TRANSL, CUT, MERGE };
	Config() :
	verbose(false), info(false), help(false), deep(false),
	mode(Mode::NONE), in(), root() { }

	bool verbose;
	bool info;
	bool help;
	bool deep;

	Mode   mode;

	string in;
	string out;
	string root;
};

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
		Timer work;
		Timer total;
	};
	template<typename T>
	using Table = Map<uint, T>;

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

	static const Mm& get() { return mod(); }
	static Mm& mod() { static Mm mm; return mm; }
};

Source* parse(string path);
smm::Source* translate(const Source* source);

}} // mdl::mm


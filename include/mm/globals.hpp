#pragma once

#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace mm {

struct Config {
	Config() :
	verbose(false), info(false), help(false),
	in(), root() { }

	bool verbose;
	bool info;
	bool help;

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
		Timer translate;
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
	Block*  source;
	string  status;
	bool    failed;

	void run();
	bool parse();
	bool translate();

	static const Mm& get() { return mod(); }
	static Mm& mod() { static Mm mm; return mm; }
};

ostream& operator << (ostream& os, const Mm& s);
Block* parse(const string& path, Block* src = nullptr);
smm::Source* translate(const Block* source);

}} // mdl::mm


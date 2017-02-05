#pragma once

#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace mm {

enum class Mode { NONE, TRANSL, CUT, MERGE, DEFAULT = NONE };
enum class Target { SMM, DEFAULT = SMM };
typedef mdl::Config<Mode, Target> Config;

struct Math {
	template<typename T>
	using Table = map<uint, T>;
	Table<Theorem*>   theorems;
	Table<Axiom*>     axioms;
	Table<Essential*> essentials;
	Table<Floating*>  floatings;
	vector<Theorem*>  theory;
};

typedef mdl::System<Source, Math, Config> System;

void run(System&);
Source* parse_spirit(string path);
Source* parse_peg(string path);
Source* parse(string path);

smm::Source* translate(const Source* source);

}} // mdl::mm


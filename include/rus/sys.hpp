#pragma once

#include "rus/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace rus {

enum class Mode { NONE, TRANSL, PROVE, MONITOR, DEFAULT = NONE };
enum class Target { NONE, SMM, RUS, DEFAULT = NONE };
typedef mdl::Config<Mode, Target> Config;

struct Math {
	template<typename T>
	using Table = map<uint, T>;

	Table<Const*>   consts;
	Table<Type*>    types;
	Table<Rule*>    rules;
	Table<Axiom*>   axioms;
	Table<Def*>     defs;
	Table<Theorem*> theorems;
	Table<Proof*>   proofs;
};

typedef mdl::Sys<Source, Math, Config> System;

void run(System&);
string show(const System&);
string info(const System&);
Source* parse(string path);
void verify(Source*);
smm::Source* translate(const Source* source);

namespace parser {
	uint get_ind();
	uint inc_ind();
}

}} // mdl::rus


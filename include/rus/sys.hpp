#pragma once

#include "rus/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace rus {

enum class Mode { NONE, TRANSL, PROVE, MONITOR, DEFAULT = NONE };
enum class Target { NONE, SMM, RUS, DEFAULT = NONE };
typedef mdl::Config<Mode, Target> Config;

struct Math {
	Table<Const>   consts;
	Table<Type>    types;
	Table<Rule>    rules;
	Table<Axiom>   axioms;
	Table<Def>     defs;
	Table<Theorem> theorems;
	Table<Proof>   proofs;
	Table<Source>  sources;
};

struct Sys : public  mdl::Sys<Sys, Source, Math, Config> {
	Sys(const string& name = "default");
};

uint validate(const string& name);

namespace parser {
	uint get_ind();
	uint inc_ind();
}

}} // mdl::rus


#pragma once

#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace mm {

enum class Mode { NONE, TRANSL, CUT, MERGE, DEFAULT = NONE };
enum class Target { SMM, DEFAULT = SMM };
typedef mdl::Config<Mode, Target> Config;

struct Math {
	Table<Theorem>   theorems;
	Table<Axiom>     axioms;
	Table<Essential> essentials;
	Table<Floating>  floatings;
	Table<Source>    sources;
};

struct Sys : public  mdl::Sys<Sys, Source, Math, Config> {
	Sys(const string& name = "default");
};

uint validate(const string& name);

}} // mdl::mm


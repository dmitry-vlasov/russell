#pragma once

#include "smm/ast.hpp"
#include "mm/ast.hpp"
#include "rus/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace smm {

enum class Mode { TRANSL, DEFAULT = TRANSL };
enum class Target { TARGET_NONE, TARGET_MM, TARGET_RUS, DEFAULT = TARGET_NONE };
typedef mdl::Config<Mode, Target> Config;

struct Math {
	set<Symbol>      constants;
	Table<Assertion> assertions;
	Table<Source>    sources;
};

struct Sys : public  mdl::Sys<Sys, Source, Math, Config> {
	Sys(const string& name = "default");
};

uint validate(const string& name);

void run(Sys&);
mm::Source*  translate_to_mm(const Source* source);
rus::Source* translate_to_rus(const Source* source);

}} // mdl::smm


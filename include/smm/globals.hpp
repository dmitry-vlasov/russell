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
	set<Symbol>        constants;
	vector<Assertion*> assertions;
};

typedef mdl::System<Source, Math, Config> System;

void run(System&);
string show(System&);
Source* parse(string path);
void verify(const vector<Assertion*>& theory);
mm::Source*  translate_to_mm(const Source* source);
rus::Source* translate_to_rus(const Source* source);

}} // mdl::smm


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
	template<typename T>
	using Table = map<uint, T>;
	set<Symbol>        constants;
	Table<Assertion*> assertions;
};

typedef mdl::Sys<Source, Math, Config> System;

void run(System&);
string show(const System&);
string info(const System&);
Source* parse(string path);
void verify();
mm::Source*  translate_to_mm(const Source* source);
rus::Source* translate_to_rus(const Source* source);

}} // mdl::smm


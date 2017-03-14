#pragma once

#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace mm {

struct Math {
	Table<Theorem>   theorems;
	Table<Axiom>     axioms;
	Table<Essential> essentials;
	Table<Floating>  floatings;
	Table<Source>    sources;

	~Math() { sources.destroy(); }
};

struct Sys : public mdl::Sys<Sys, Math> {
	Sys();
};

void run();
string show();
string info();
Source* parse(const Path& path);
smm::Source* translate(const Source* source);

}} // mdl::mm


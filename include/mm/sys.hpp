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
	string show() const;
	string info() const;
};

struct Sys : public mdl::Sys<Sys, Math> { Sys(); };

void run();

}} // mdl::mm


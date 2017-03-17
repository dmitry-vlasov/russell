#pragma once

#include "smm/ast.hpp"
#include "mm/ast.hpp"
#include "rus/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace smm {

struct Math {
	set<Symbol>      constants;
	Table<Assertion> assertions;
	Table<Source>    sources;

	~Math() { sources.destroy(); }
	string show() const;
	string info() const;
};

struct Sys : public mdl::Sys<Sys, Math> { Sys(); };

void run();

}} // mdl::smm


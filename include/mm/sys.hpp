#pragma once

#include "common.hpp"

namespace mdl { namespace mm {

class Theorem;
class Axiom;
class Essential;
class Floating;
class Source;

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


#pragma once

#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace mm {

struct Math {
	template<typename T>
	using Table = map<uint, T>;

	Table<Theorem*>   theorems;
	Table<Axiom*>     axioms;
	Table<Essential*> essentials;
	Table<Floating*>  floatings;
	Table<Source*>    sources;

	~Math() { for (auto s : sources) delete s.second; }
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


#pragma once

#include "smm/ast.hpp"
#include "mm/ast.hpp"
#include "rus/ast.hpp"
#include "timer.hpp"

namespace mdl { namespace smm {

struct Math {
	template<typename T>
	using Table = map<uint, T>;

	set<Symbol>       constants;
	Table<Assertion*> assertions;
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
void verify();
mm::Source*  translate_to_mm(const Source* source);
rus::Source* translate_to_rus(const Source* source);

}} // mdl::smm

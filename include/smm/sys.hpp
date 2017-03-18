#pragma once

#include "common.hpp"

namespace mdl { namespace smm {

class Assertion;
class Source;

struct Math {
	set<Symbol>      constants;
	Table<Assertion> assertions;
	Table<Source>    sources;

	~Math();
	string show() const;
	string info() const;
};

struct Sys : public mdl::Sys<Sys, Math> { Sys(); };

void run();

}} // mdl::smm


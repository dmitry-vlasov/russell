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

	template<class T>
	Table<T>& get();
	template<class T>
	const Table<T>& get() const;
};

struct Sys : public mdl::Sys<Sys, Math> {
	Sys(uint);
	string lang() const override { return  "smm"; }
};

template<class T>
using User = mdl::User<T, Sys>;

template<class T>
using Owner = mdl::Owner<T, Sys>;

void run();

}} // mdl::smm


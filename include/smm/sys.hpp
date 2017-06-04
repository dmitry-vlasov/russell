#pragma once

#include "common.hpp"

namespace mdl { namespace smm {

class Assertion;
class Source;

struct Math {
	set<Symbol>      constants;
	Table<Assertion> assertions;
	Table<Source>    sources;

	string show() const;
	string info() const;
	void destroy();

	template<class T>
	Table<T>& get();
	template<class T>
	const Table<T>& get() const;
};

struct Sys : public mdl::Sys<Sys, Math> {
	Sys(uint id) : mdl::Sys<Sys, Math>(id) { }
	static string descr() { return "smm"; }
	static string lang() { return "smm"; }
	static string ext() { return "smm"; }
	static const Actions& actions();
};

template<class T>
using User = mdl::User<T, Sys>;

template<class T>
using Owner = mdl::Owner<T, Sys>;

}} // mdl::smm


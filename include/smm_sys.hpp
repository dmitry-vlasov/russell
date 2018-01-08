#pragma once

#include "common.hpp"
#include "smm_expr.hpp"

namespace mdl { namespace smm {

class Constant;
class Assertion;
class Source;

class Math {
	Table<Constant>  constants;
	Table<Assertion> assertions;
	Table<Source>    sources;
public :

	string show() const;
	string info() const;
	void destroy();

	template<class T>
	Table<T>& get();
	template<class T>
	const Table<T>& get() const;
};

struct Sys : public mdl::Sys<Sys, Math> {
	typedef Source Src;
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


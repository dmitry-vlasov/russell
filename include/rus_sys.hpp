#pragma once

#include "common.hpp"

namespace mdl { namespace rus {

class Constant;
class Type;
class Rule;
class Axiom;
class Def;
class Theorem;
class Proof;
class Source;
class Assertion;

class Math {
	Table<Constant>  consts;
	Table<Type>      types;
	Table<Rule>      rules;
	Table<Assertion> assertions;
	Table<Source>    sources;
public:

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
	static string descr() { return "rus"; }
	static string lang() { return "rus"; }
	static string ext() { return "rus"; }
	static const Actions& actions();
};

template<class T>
using User = mdl::User<T, Sys>;

template<class T>
using Owner = mdl::Owner<T, Sys>;

}} // mdl::rus


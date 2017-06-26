#pragma once

#include "common.hpp"

namespace mdl { namespace mm {

class Theorem;
class Axiom;
class Essential;
class Floating;
class Source;

class Math {
	Table<Theorem>   theorems;
	Table<Axiom>     axioms;
	Table<Essential> essentials;
	Table<Floating>  floatings;
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
	Sys(uint id) : mdl::Sys<Sys, Math>(id) { }
	static string descr() { return "mm"; }
	static string lang() { return "mm"; }
	static string ext() { return "mm"; }
	static const Actions& actions();
};

template<class T>
using User = mdl::User<T, Sys>;

template<class T>
using Owner = mdl::Owner<T, Sys>;

}} // mdl::mm


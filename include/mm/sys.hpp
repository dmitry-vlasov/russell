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

	~Math();
	string show() const;
	string info() const;

	template<class T>
	Table<T>& get();
	template<class T>
	const Table<T>& get() const;
};

struct Sys : public mdl::Sys<Sys, Math> {
	Sys(const string& n);
};

template<class T>
using User = mdl::User<T, Sys>;

template<class T>
using Owner = mdl::Owner<T, Sys>;


void run();

}} // mdl::mm


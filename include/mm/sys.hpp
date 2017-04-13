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

template<>
inline Table<Theorem>& Math::get<Theorem>() { return theorems; }
template<>
inline Table<Axiom>& Math::get<Axiom>() { return axioms; }
template<>
inline Table<Essential>& Math::get<Essential>() { return essentials; }
template<>
inline Table<Floating>& Math::get<Floating>() { return floatings; }
template<>
inline Table<Source>& Math::get<Source>() { return sources; }

template<>
inline const Table<Theorem>& Math::get<Theorem>() const { return theorems; }
template<>
inline const Table<Axiom>& Math::get<Axiom>() const { return axioms; }
template<>
inline const Table<Essential>& Math::get<Essential>() const { return essentials; }
template<>
inline const Table<Floating>& Math::get<Floating>() const { return floatings; }
template<>
inline const Table<Source>& Math::get<Source>() const { return sources; }

struct Sys : public mdl::Sys<Sys, Math> { Sys(); };

void run();

}} // mdl::mm


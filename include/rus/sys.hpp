#pragma once

#include "common.hpp"

namespace mdl {

namespace smm { class Source; }

namespace rus {

/*
struct Math {
	struct Counter {
		Counter() : c(0) { }
		uint get() { return c; }
		uint inc() { return c++; }
	private:
		uint c;
	};

	Table<Const>   consts;
	Table<Type>    types;
	Table<Rule>    rules;
	Table<Axiom>   axioms;
	Table<Def>     defs;
	Table<Theorem> theorems;
	Table<Proof>   proofs;
	Table<Source>  sources;
	Counter        ind;

	~Math() { sources.destroy(); }
};

 */

class Const;
class Type;
class Rule;
class Axiom;
class Def;
class Theorem;
class Proof;
class Source;

struct Math {
	template<typename T>
	using Table1 = map<uint, T>;

	Table<Const>    consts;
	Table<Type>     types;
	Table<Rule>     rules;

	Table1<Axiom*>   axioms;
	Table1<Def*>     defs;
	Table1<Theorem*> theorems;

	Table<Proof>   proofs;
	Table<Source>  sources;

	~Math();

	template<class T>
	Table<T>& get();
	template<class T>
	const Table<T>& get() const;
};

template<>
inline Table<Const>& Math::get<Const>() { return consts; }
template<>
inline Table<Type>& Math::get<Type>() { return types; }
template<>
inline Table<Rule>& Math::get<Rule>() { return rules; }
template<>
inline Table<Source>& Math::get<Source>() { return sources; }

template<>
inline const Table<Const>& Math::get<Const>() const { return consts; }
template<>
inline const Table<Type>& Math::get<Type>() const { return types; }
template<>
inline const Table<Rule>& Math::get<Rule>() const { return rules; }
template<>
inline const Table<Source>& Math::get<Source>() const { return sources; }

struct Sys : public mdl::Sys<Sys, Math> {
	Sys();
};

template<class T>
using User = mdl::User<T, Sys>;

template<class T>
using Owner = mdl::Owner<T, Sys>;

void run();
string show();
string info();
Source* parse(Path path);
void verify(const Source*);
smm::Source* translate(const Source* source);

}} // mdl::rus


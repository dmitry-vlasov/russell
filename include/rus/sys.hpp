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
class Assertion;

struct Math {
	template<typename T>
	using Table1 = map<uint, T>;

	Table<Const>    consts;
	Table<Type>     types;
	Table<Rule>     rules;

	Table<Assertion>   assertions;

	Table<Proof>   proofs;
	Table<Source>  sources;

	~Math();

	template<class T>
	Table<T>& get();
	template<class T>
	const Table<T>& get() const;
};

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


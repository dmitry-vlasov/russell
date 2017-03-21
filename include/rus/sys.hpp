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
	Table1<Type*>    types;
	Table1<Rule*>    rules;
	Table1<Axiom*>   axioms;
	Table1<Def*>     defs;
	Table1<Theorem*> theorems;
	Table1<Proof*>   proofs;
	Table1<Source*>  sources;

	~Math();
};

struct Sys : public mdl::Sys<Sys, Math> {
	Sys();
};

void run();
string show();
string info();
Source* parse(Path path);
void verify(Source*);
smm::Source* translate(const Source* source);

}} // mdl::rus


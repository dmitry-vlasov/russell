#pragma once

#include "common.hpp"

namespace mdl {

namespace smm { class Source; }

namespace rus {

class Const;
class Type;
class Rule;
class Axiom;
class Def;
class Theorem;
class Proof;
class Source;
class Assertion;

class Math {
	Table<Const>     consts;
	Table<Type>      types;
	Table<Rule>      rules;
	Table<Assertion> assertions;
	Table<Proof>     proofs;
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
	Sys();
};

template<class T>
using User = mdl::User<T, Sys>;

template<class T>
using Owner = mdl::Owner<T, Sys>;

void run();

}} // mdl::rus


#pragma once

#include "common.hpp"

namespace mdl { namespace mm {

class Source;
class Assertion;
class Var;

struct VarDecl  {
	VarDecl(uint l, uint t, uint v) : label(l), type(t), var(v) { }
	uint label;
	uint type;
	uint var;
	Var* make(bool inner, uint index) const;
};

class Math {
	Table<Assertion> assertions;
	Table<Source>    sources;
public:
	vector<VarDecl> decls;
	map<uint, uint> consts;

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


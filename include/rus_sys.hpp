#pragma once

#include "common.hpp"

namespace mdl {
namespace mm { class Source; }
namespace rus {

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

struct SrcPos : Writable {
	Source* src = nullptr;
	uint    pos = 0;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

template<class T>
using User = mdl::User<T, Sys>;

template<class T>
using Owner = mdl::Owner<T, Sys>;

void verify(uint src = -1);
mm::Source* translate(uint src, uint tgt);
void parse_src_peg();
void parse_src_spirit();
void read(uint src);
void min_imports(uint src = -1);
Return lookup_ref(uint src, uint line, uint col, string what);
SrcPos insert_theorem(unique_ptr<Theorem>& thm);

string xml_outline(const Source&, uint);
string xml_structure(uint bits);
string xml_types();

void reduce_duplicate_steps(const string& opts);
void reduce_unused_steps(const string& opts);
void factorize_subproofs(const string& opts);
void reduce_unused_hyps(const string& opts);
void reduce_proof_shortcuts(const string& opts);
void generalize_theorems(const string& opts);
void generaliziation_relation(const string& opts);
void replace_with_optimal(const string& opts);

string report_stats(const string& opts);


}} // mdl::rus


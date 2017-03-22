#include "rus/ast.hpp"

namespace mdl { namespace rus {


Const::Const(Symbol s, Symbol a, Symbol l) : symb(s), ascii(a), latex(l) {
	Sys::mod().math.consts.add(symb.lit, this);
}
Const::~Const() {
	Sys::mod().math.consts.del(symb.lit);
}

Type::Type(uint i) : id(i) {
	Sys::mod().math.types.add(id, this);
}
Type::Type(uint i, const vector<Type*>& s) : id(i), sup(s) {
	Sys::mod().math.types.add(id, this);
}
Type::~Type() {
	Sys::mod().math.types.del(id);
	for (auto p : supers) delete p.second;
}

Rule::Rule(uint i) : id(i), type(nullptr) {
	Sys::mod().math.rules.add(id, this);
}
Rule::~Rule() {
	Sys::mod().math.rules.del(id);
}

Source::Source(uint label) : mdl::Source<Source, Sys>(label), theory(nullptr) {
	Sys::mod().math.sources[label] = this;
}
Source::~Source() {
	if (theory) delete theory;
}

}} // mdl::rus

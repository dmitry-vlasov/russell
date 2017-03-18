#include "rus/ast.hpp"
#include "rus/sys.hpp"

namespace mdl { namespace rus {

/*
Const::Const(uint i, Symbol s, Symbol a, Symbol l) : ind(i), symb(s), ascii(a), latex(l) {
	Sys::mod().math.consts.add(symb.lit, this);
}
Const::~Const() {
	Sys::mod().math.consts.del(symb.lit);
}

Type::Type(uint i) : ind(Sys::mod().math.ind.inc()), id(i), sup(), supers(), rules() {
	Sys::mod().math.types.add(id, this);
}
Type::~Type() {
	Sys::mod().math.types.del(id);
	for (auto p : supers) delete p.second;
}

 */


Source::Source(uint l) : label(l), data(), theory(nullptr) {
	Sys::mod().math.sources[label] = this;
}
Source::~Source() {
	if (theory) delete theory;
}
Path Source::path() const {
	return Sys::conf().in.relative(name());
}
void Source::read() {
	path().read(data);
}
void Source::write() {
	path().write(data);
}

}} // mdl::rus

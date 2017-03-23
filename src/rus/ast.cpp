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

Assertion::Assertion(uint i) : id(i) {
	//Sys::mod().math.assertions.add(id, this);
}
Assertion::~Assertion() {
	//Sys::mod().math.assertions.del(id);
	for (auto h : hyps) delete h;
	for (auto p : props) delete p;
}

Axiom::Axiom(uint id) : Assertion(id) {
	Sys::mod().math.axioms[id] = this;
}

Theorem::Theorem(uint id) : Assertion(id) {
	Sys::mod().math.theorems[id] = this;
}

Def::Def(uint id) : Assertion(id) {
	Sys::mod().math.defs[id] = this;
}

Step::Step(uint i, Step::Kind sk, Assertion::Kind ak, uint id, Proof* p) :
	ind(i), kind(sk), proof(p) {
	const Math& math = Sys::get().math;
	switch (ak) {
	case Assertion::AXM :
		if (!math.axioms.count(id))
			throw Error("unknown axiom", Lex::toStr(id));
		val.ass = math.axioms.at(id); break;
	case Assertion::THM :
		if (!math.theorems.count(id))
			throw Error("unknown axiom", Lex::toStr(id));
		val.ass = math.theorems.at(id); break;
	case Assertion::DEF :
		if (!math.defs.count(id))
			throw Error("unknown axiom", Lex::toStr(id));
		val.ass = math.defs.at(id); break;
	default: assert(0 && "impossible");
	}

	/*if (kind == ASS) {
		Sys::mod().math.assertions.use(id, val.ass);
	}*/
}
Step::~Step() {
	/*if (kind == ASS) {
		Sys::mod().math.assertions.unuse(id, val.ass);
	}*/
}

Proof::Proof(Theorem* t, uint i) : id(i), thm(t), par(nullptr), has_id(!Undef<uint>::is(id)) {
	static uint fresh = 0;
	if (!has_id) id = Lex::toInt(string("__proof_") + to_string(fresh++));
	Sys::mod().math.proofs.add(id, this);
}
Proof::~Proof() {
	Sys::mod().math.proofs.del(id);
	for (auto& e : elems) e.destroy();
}

Source::Source(uint label) : mdl::Source<Source, Sys>(label), theory(nullptr) {
	Sys::mod().math.sources.add(label, this);
}
Source::~Source() {
	Sys::mod().math.sources.del(label);
	if (theory) delete theory;
}

}} // mdl::rus

#include "rus/ast.hpp"

namespace mdl { namespace rus {


Const::Const(Symbol s, Symbol a, Symbol l) : symb(s), ascii(a), latex(l) {
	Sys::mod().math.get<Const>().add(symb.lit, this);
}
Const::~Const() {
	Sys::mod().math.get<Const>().del(symb.lit);
}

Type::Type(uint i) : id(i) {
	Sys::mod().math.get<Type>().add(id, this);
}
Type::Type(uint i, const vector<Type*>& s) : id(i), sup(s) {
	Sys::mod().math.get<Type>().add(id, this);
}
Type::~Type() {
	Sys::mod().math.get<Type>().del(id);
	for (auto p : supers) delete p.second;
}

Rule::Rule(uint i) : id(i), type(nullptr) {
	Sys::mod().math.get<Rule>().add(id, this);
	//Sys::mod().math.rules.use(id, type->rules.add(term));
}
Rule::~Rule() {
	//Sys::mod().math.rules.unuse(id, type->rules.add(term));
	Sys::mod().math.get<Rule>().del(id);
}

Assertion::Assertion(uint i) : id_(i) {
	//Sys::mod().math.assertions.add(id, this);
}
Assertion::~Assertion() {
	//Sys::mod().math.assertions.del(id);
	for (auto h : hyps) delete h;
	for (auto p : props) delete p;
}

Axiom::Axiom(uint id) : Assertion(id) {
	//Sys::mod().math.axioms[id] = this;
	Sys::mod().math.get<Assertion>().add(id, this);
}

Theorem::Theorem(uint id) : Assertion(id) {
	//Sys::mod().math.theorems[id] = this;
	Sys::mod().math.get<Assertion>().add(id, this);
}

Def::Def(uint id) : Assertion(id) {
	//Sys::mod().math.defs[id] = this;
	Sys::mod().math.get<Assertion>().add(id, this);
}

Step::Step(uint i, Step::Kind sk, Assertion::Kind ak, uint id, Proof* p) :
	ind_(i), kind_(sk), proof_(p) {
	Math& math = Sys::mod().math;
	if (!math.get<Assertion>().has(id)) {
		throw Error("unknown assertion", Lex::toStr(id));
	}
	val_.ass = new User<Assertion>(id);
	switch (ak) {
	case Assertion::AXM :
		if (!dynamic_cast<Axiom*>(val_.ass->get()))
			throw Error("not an axiom", Lex::toStr(id));
		break;
	case Assertion::THM :
		if (!dynamic_cast<Theorem*>(val_.ass->get()))
			throw Error("not a theorem", Lex::toStr(id));
		break;
	case Assertion::DEF :
		if (!dynamic_cast<Def*>(val_.ass->get()))
			throw Error("not a definition", Lex::toStr(id));
		break;
	default: assert(false && "impossible");
	}

	/*if (kind == ASS) {
		Sys::mod().math.assertions.use(id, val.ass);
	}*/
}
Step::~Step() {
	//if (kind_ == ASS) delete val_.ass;
}

Proof::Proof(Theorem* t, uint i) : id(i), thm(t), par(nullptr), has_id(!Undef<uint>::is(id)) {
	static uint fresh = 0;
	if (!has_id) id = Lex::toInt(string("__proof_") + to_string(fresh++));
	Sys::mod().math.get<Proof>().add(id, this);
}
Proof::~Proof() {
	Sys::mod().math.get<Proof>().del(id);
	for (auto& e : elems) e.destroy();
}

Source::Source(uint label) : mdl::Source<Source, Sys>(label), theory(nullptr) {
	//Sys::mod().math.sources.add(label, this);
}
Source::~Source() {
	//Sys::mod().math.sources.del(label);
	if (theory) delete theory;
}

}} // mdl::rus

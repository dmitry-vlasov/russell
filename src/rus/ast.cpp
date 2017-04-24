#include "rus/ast.hpp"

namespace mdl { namespace rus {


Const::Const(Symbol s, Symbol a, Symbol l) : Owner(s.lit), symb(s), ascii(a), latex(l) { }

Type::Type(uint i) : Owner(i) { }
Type::Type(uint i, const vector<Type*>& s) : Owner(i), sup(s) { }
Type::~Type() {
	for (auto p : supers) delete p.second;
}

Rule::Rule(uint id, uint tp) : Owner(id), type(tp) { }
Rule::Rule(uint id, uint tp, const Vars& v) :
	Owner(id), type(tp), vars(v) { }

Assertion::Assertion(uint i) : Owner(i) { }
Assertion::~Assertion() {
	for (auto h : hyps) delete h;
	for (auto p : props) delete p;
}

Axiom::Axiom(uint id) : Assertion(id) { }
Theorem::Theorem(uint id) : Assertion(id) { }
Def::Def(uint id) : Assertion(id) { }

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

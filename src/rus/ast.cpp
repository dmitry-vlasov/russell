#include <rus_ast.hpp>

namespace mdl { namespace rus {

Type::Type(uint i, const Token& t) : Tokenable(t), Owner(i) { }
Type::Type(uint i, const vector<Type*>& s, const Token& t) : Tokenable(t), Owner(i) {
	for (auto t : s) sup.push_back(t);
}
Type::~Type() {
	for (auto p : supers) delete p.second;
}

Rule::Rule(uint id, uint tp, const Token& t) :
	Tokenable(t), Owner(id), type(tp) { }
Rule::Rule(uint id, uint tp, const Vars& v, const Token& t) :
	Tokenable(t), Owner(id), type(tp), vars(v) { }

Assertion::Assertion(uint i, const Token& t) : Tokenable(t), Owner(i) { }
Assertion::~Assertion() {
	for (auto h : hyps) delete h;
	for (auto p : props) delete p;
}

Axiom::Axiom(uint id, const Token& t) : Assertion(id, t) { }
Theorem::Theorem(uint id, const Token& t) : Assertion(id, t) { }
Def::Def(uint id, const Token& t) : Assertion(id, t) { }

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
	if (kind_ == ASS) delete val_.ass;
}

inline uint make_proof_id(uint id, const Theorem* th) {
	if (Undef<uint>::is(id)) {
		const string& th_name = Lex::toStr(th->id());
		return Lex::toInt(string("_proof_of_") + th_name + "_" + to_string(th->proofs.size()));
	} else return id;
}

Proof::Proof(Theorem* th, uint id) : Owner(make_proof_id(id, th)), thm(th), par(nullptr) {
}
Proof::~Proof() {
	for (auto& e : elems) e.destroy();
}

Source::Source(uint label) : mdl::Source<Source, Sys>(label), theory(nullptr) { }
Source::~Source() {
	if (theory) delete theory;
}

}} // mdl::rus

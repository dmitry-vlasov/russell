#include <rus_ast.hpp>

namespace mdl { namespace rus {

Type::Type(Id i, const Token& t) : Owner(i.id, t) { }
Type::Type(Id i, const vector<Id>& s, const Token& t) : Owner(i.id, t) {
	for (auto t : s) sup.push_back(User<Type>(t));
}
Type::~Type() {
	for (auto p : supers) delete p.second;
}

Rule::Rule(Id i, const Token& t) :
	Owner(i.id, t) { }
Rule::Rule(Id i, const Vars& v, const Token& t) :
	Owner(i.id, t), vars(v) { }

Assertion::Assertion(Id i, const Token& t) : Owner(i.id, t) { }
Assertion::~Assertion() {
	for (auto h : hyps) delete h;
	for (auto p : props) delete p;
}

Axiom::Axiom(Id id, const Token& t) : Assertion(id, t) { }
Theorem::Theorem(Id id, const Token& t) : Assertion(id, t) { }
Def::Def(Id id, const Token& t) : Assertion(id, t) { }

Step::Step(uint i, Step::Kind sk, Assertion::Kind ak, Id id, Proof* p, const Token& t) :
	Tokenable(t), ind_(i), kind_(sk), proof_(p) {
	Math& math = Sys::mod().math;
	if (!math.get<Assertion>().has(id.id)) {
		throw Error("unknown assertion", id.toStr());
	}
	val_.ass = new User<Assertion>(id);
	switch (ak) {
	case Assertion::AXM :
		if (!dynamic_cast<Axiom*>(val_.ass->get()))
			throw Error("not an axiom", id.toStr());
		break;
	case Assertion::THM :
		if (!dynamic_cast<Theorem*>(val_.ass->get()))
			throw Error("not a theorem", id.toStr());
		break;
	case Assertion::DEF :
		if (!dynamic_cast<Def*>(val_.ass->get()))
			throw Error("not a definition", id.toStr());
		break;
	default: assert(false && "impossible");
	}

	/*if (kind == ASS) {
		Sys::mod().math.assertions.use(id, val.ass);
	}*/
}
Step::~Step() {
	if (kind_ == ASS) delete val_.ass;
	for (Ref* ref : refs) delete ref;
}

inline uint make_proof_id(uint id, const Theorem* th) {
	if (Undef<uint>::is(id)) {
		const string& th_name = Lex::toStr(th->id());
		return Lex::toInt(string("_proof_of_") + th_name + "_" + to_string(th->proofs.size()));
	} else return id;
}

Proof::Proof(Theorem* th, Id i, const Token& t) :
	Owner(make_proof_id(i.id, th), t), thm(th), par(nullptr) {
}
Proof::~Proof() {
	for (auto& e : elems) e.destroy();
}

Source::Source(uint label) : mdl::Source<Source, Sys>(label), theory(nullptr) { }
Source::~Source() {
	if (theory) delete theory;
}

}} // mdl::rus

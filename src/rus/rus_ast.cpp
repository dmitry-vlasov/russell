#include <rus_ast.hpp>

namespace mdl { namespace rus {

inline uint create_id(string pref, string s1, string s2) {
	return Lex::toInt(pref + "_" + s1 + "_" + s2);
}

inline Symbol create_var(string str, Type* tp) {
	return Symbol(Lex::toInt(str), tp);
}

inline Symbol create_const(string str, Const* c) {
	return Symbol(Lex::toInt(str), c);
}

static Rule* create_super(Type* inf, Type* sup) {
	uint id = create_id("sup", show_id(inf->id()), show_id(sup->id()));
	return new Rule(id, Vars({create_var("x", inf)}), Expr(sup->id(), {create_var("x", inf)}));
}

static void collect_super_rules(Type* inf, Type* s) {
	for (auto& sup : s->sup) {
		Rule* super = create_super(inf, sup.get());
		inf->supers[sup.get()] = super;
		collect_super_rules(inf, sup.get());
	}
}

Type::Type(Id i, const vector<Id>& s, const Token& t) : Owner(i.id, t) {
	for (auto t : s) sup.push_back(User<Type>(t));
	collect_super_rules(this, this);
}
Type::~Type() {
	for (auto p : supers) delete p.second;
}

Rule::Rule(Id i, const Vars& v, const Expr& e, const Token& t) :
	Owner(i.id, t), vars(v), term(e) {
	Tree::Children children;
	for (auto& s : term.symbols) {
		if (s.type()) children.push_back(make_unique<Tree>(s));
	}
	term.tree.reset(new Tree(this, children));
	term.type.get()->rules.add(term, i.id);
}

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
	th->proofs.push_back(User<Proof>(id()));
	assert(this == th->proofs.back().get());
}
Proof::~Proof() {
	for (auto& e : elems) e.destroy();
}

Source::Source(uint label) :
	mdl::Source<Source, Sys>(label), theory() { }
Source::~Source() {
	if (theory) delete theory;
}

}} // mdl::rus

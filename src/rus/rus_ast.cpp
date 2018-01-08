#include <rus_ast.hpp>

namespace mdl { namespace rus {

inline uint create_id(string pref, string s1, string s2) {
	return Lex::toInt(pref + "_" + s1 + "_" + s2);
}

inline Symbol create_var(string str, Type* tp) {
	return Symbol(Lex::toInt(str), tp->id(), Symbol::VAR);
}

inline Symbol create_const(string str, Const* c) {
	return Symbol(Lex::toInt(str), c->id(), Symbol::CONST);
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
	term.tree = std::move(Tree(i, children));
}

Assertion::Assertion(Id i, const Token& t) : Owner(i.id, t) { }
Assertion::~Assertion() {
	for (auto h : hyps) delete h;
	for (auto p : props) delete p;
}

Axiom::Axiom(Id id, const Token& t) : Assertion(id, t) { }
Theorem::Theorem(Id id, const Token& t) : Assertion(id, t) { }
Def::Def(Id id, const Token& t) : Assertion(id, t) { }

Step::Step(uint i, Step::Kind sk, Id id, Proof* p, const Token& t) :
	Tokenable(t), ind_(i), kind_(sk), proof_(p) {
	/*Math& math = Sys::mod().math;
	if (!math.get<Assertion>().has(id.id)) {
		throw Error("unknown assertion", id.toStr());
	}*/
	val_.ass = new User<Assertion>(id);
}
Step::~Step() {
	if (kind_ == ASS) delete val_.ass;
	for (Ref* ref : refs) delete ref;
}

inline uint make_proof_id(uint id, Id th) {
	if (Undef<uint>::is(id)) {
		const string& th_name = Lex::toStr(th.id);
		if (const Theorem* thm = dynamic_cast<const Theorem*>(Sys::get().math.get<Assertion>().access(th.id)))
			return Lex::toInt(string("_proof_of_") + th_name + "_" + to_string(thm->proofs.size()));
		else
			throw Error("not a theorem", th_name);
	} else return id;
}

Proof::Proof(Id th, Id i, const Token& t) :
	Owner(make_proof_id(i.id, th), t), thm(th), par(nullptr) {
	theorem()->proofs.emplace_back(User<Proof>(id()));
	assert(this == theorem()->proofs.back().get());
}
Proof::~Proof() {
	for (auto& e : elems) e.destroy();
}

inline Tokenable* find(Const* c, const Token& t) {
	return c->token.includes(t) ? c : nullptr;
}

inline Tokenable* find(Type* tp, const Token& t) {
	return tp->token.includes(t) ? tp : nullptr;
}

inline Tokenable* find(Rule* r, const Token& t) {
	if (r->token.includes(t)) return nullptr;
	if (r->vars.token.includes(t)) return &r->vars;
	if (r->term.token.includes(t)) return &r->term;
	return r;
}

inline Tokenable* find(Assertion* a, const Token& t) {
	if (!a->token.includes(t)) return nullptr;
	if (a->vars.token.includes(t)) return &a->vars;
	if (a->disj.token.includes(t)) return &a->disj;
	for (auto h : a->hyps) if (h->token.includes(t)) return h;
	for (auto p : a->props) if (p->token.includes(t)) return p;
	return a;
}

inline Tokenable* find(Def* d, const Token& t) {
	if (!d->token.includes(t)) return nullptr;
	if (d->dfm.token.includes(t)) return &d->dfm;
	if (d->dfs.token.includes(t)) return &d->dfs;
	if (d->prop.token.includes(t)) return &d->prop;
	return find(static_cast<Assertion*>(d), t);
}

inline Tokenable* find(Qed* q, const Token& t) {
	return q->token.includes(t) ? q : nullptr;
}

inline Tokenable* find(Step* s, const Token& t) {
	return s->token.includes(t) ? s : nullptr;
}

inline Tokenable* find(Vars* v, const Token& t) {
	return v->token.includes(t) ? v : nullptr;
}

inline Tokenable* find(Proof::Elem& e, const Token& t) {
	switch (e.kind) {
	case Proof::Elem::QED: return find(e.val.qed, t);
	case Proof::Elem::STEP: return find(e.val.step, t);
	case Proof::Elem::VARS: return find(e.val.vars, t);
	default: return nullptr;
	}
}

inline Tokenable* find(Proof* p, const Token& t) {
	if (!p->token.includes(t)) return nullptr;
	for (auto e : p->elems) if (Tokenable* ret = find(e, t)) return ret;
	return p;
}

inline Tokenable* find(Import* i, const Token& t) {
	return i->token.includes(t) ? i : nullptr;
}

Tokenable* find(Node& n, const Token& t);

inline Tokenable* find(Theory* th, const Token& t) {
	for (auto& n : th->nodes)
		if (Tokenable* ret = find(n, t)) return ret;
	return nullptr;
}

Tokenable* find(Node& n, const Token& t) {
	switch (n.kind) {
	case Node::NONE: return nullptr;
	case Node::CONST:   if (Tokenable* ret = find(n.val.cst, t)) return ret; else return nullptr;
	case Node::TYPE:    if (Tokenable* ret = find(n.val.tp, t)) return ret; else return nullptr;
	case Node::RULE:    if (Tokenable* ret = find(n.val.rul, t)) return ret; else return nullptr;
	case Node::AXIOM:   if (Tokenable* ret = find(n.val.ax, t)) return ret; else return nullptr;
	case Node::DEF:     if (Tokenable* ret = find(n.val.def, t)) return ret; else return nullptr;
	case Node::THEOREM: if (Tokenable* ret = find(n.val.thm, t)) return ret; else return nullptr;
	case Node::PROOF:   if (Tokenable* ret = find(n.val.prf, t)) return ret; else return nullptr;
	case Node::THEORY:  if (Tokenable* ret = find(n.val.thy, t)) return ret; else return nullptr;
	case Node::IMPORT:  if (Tokenable* ret = find(n.val.imp, t)) return ret; else return nullptr;
	case Node::COMMENT: return nullptr;
	}
	return nullptr;
}

Source::Source(uint label) :
	mdl::Source<Source, Sys>(label), theory(nullptr) { }
Source::~Source() {
	if (theory) delete theory;
}
Tokenable* Source::find(const Token& t) {
	return theory ? rus::find(theory, t) : nullptr;
}


}} // mdl::rus

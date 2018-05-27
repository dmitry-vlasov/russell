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
		inf->supers[sup.get()].reset(super);
		collect_super_rules(inf, sup.get());
	}
}

Type::Type(Id i, const vector<Id>& s, const Token& t) : Owner(i.id, t) {
	for (auto t : s) sup.push_back(User<Type>(t));
	collect_super_rules(this, this);
}

Rule::Rule(Id i, const Vars& v, const Expr& e, const Token& t) :
	Owner(i.id, t), vars(v), term(e) {
	Tree::Children children;
	for (auto& s : term.symbols) {
		if (s.var) children.push_back(make_unique<Tree>(s));
	}
	term.set(new Tree(i, children));
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

inline void check_disjointed(const set<uint>& s1, const set<uint>& s2) {
	if (s1.size() > s2.size()) return check_disjointed(s2, s1);
	for (uint x : s1) {
		if (s2.find(x) != s2.end()) {
			throw Error("disjointed variable restriction violation", Lex::toStr(x));
		}
	}
}

void Disj::check(const Substitution& s, const Theorem* t) const {
	for (const auto& dis : d) {
		for (uint v1 : dis) {
			if (!s.mapsVar(v1)) continue;
			set<uint> v1_vars = s.sub().at(v1).vars();
			for (uint v2 : dis) {
				if (v1 == v2 || !s.mapsVar(v2)) continue;
				set<uint> v2_vars = s.sub().at(v2).vars();
				check_disjointed(v1_vars, v2_vars);
				t->disj.pairs_are_disjointed(v1_vars, v2_vars);
			}
		}
	}
}

void Disj::check(const Substitution& s, Theorem* t) const {
	for (const auto& dis : d) {
		for (uint v1 : dis) {
			if (!s.mapsVar(v1)) continue;
			set<uint> v1_vars = s.sub().at(v1).vars();
			for (uint v2 : dis) {
				if (v1 == v2 || !s.mapsVar(v2)) continue;
				set<uint> v2_vars = s.sub().at(v2).vars();
				check_disjointed(v1_vars, v2_vars);
				t->disj.make_pairs_disjointed(v1_vars, v2_vars);
			}
		}
	}
}

void Disj::pairs_are_disjointed(const set<uint>& vars1, const set<uint>& vars2) const {
	if (vars1.empty() || vars2.empty()) return;
	for (uint v1 : vars1) {
		if (dmap.find(v1) == dmap.end()) {
			throw Error("disjointed variable is not inherently disjointed", Lex::toStr(v1));
		}
		const set<uint>& dis = dmap.at(v1);
		for (uint v2 : vars2) {
			if (dis.find(v2) == dis.end()) {
				throw Error("disjointed variable is not inherently disjointed", Lex::toStr(v1) + ", " + Lex::toStr(v2));
			}
		}
	}
}

void Disj::make_pairs_disjointed(const set<uint>& vars1, const set<uint>& vars2) {
	if (vars1.empty() || vars2.empty()) return;
	for (uint v1 : vars1) {
		for (uint v2 : vars2) {
			if (v1 != v2) {
				dmap[v1].insert(v2);
				dmap[v2].insert(v1);
			}
		}
	}
}

void Disj::init_dmap() {
	for (const auto& dis : d) {
		for (uint v1 : dis) {
			for (uint v2 : dis) {
				if (v1 != v2) {
					dmap[v1].insert(v2);
				}
			}
		}
	}
}

inline bool are_disj(const map<uint, set<uint>>& dmap, uint v1, uint v2) {
	auto p = dmap.find(v1);
	if (p != dmap.end()) {
		const set<uint>& dis = p->second;
		return dis.find(v2) != dis.end();
	} else {
		return false;
	}
}

void addPair(map<uint, set<uint>>& dmap, vector<set<uint>>& d, uint v1, uint v2) {

	auto try_to_extend = [&dmap](set<uint>& dis, uint v1, uint v2) {
		bool can_be_added = true;
		if (dis.find(v1) != dis.end()) {
			for (uint d : dis) {
				if (!are_disj(dmap, d, v2)) {
					can_be_added = false;
				}
			}
		}
		if (can_be_added) {
			dis.insert(v2);
		}
		return can_be_added;
	};

	for (auto& dis : d) {
		if (try_to_extend(dis, v1, v2)) return;
		if (try_to_extend(dis, v2, v1)) return;
	}
	d.push_back(set<uint>());
	d.back().insert(v1);
	d.back().insert(v2);
}

void Disj::init_d() {
	for (const auto& p : dmap) {
		uint v1 = p.first;
		for (uint v2 : p.second) {
			addPair(dmap, d, v1, v2);
		}
	}
}

Proof::Proof(Id th, Id i, const Token& t) :
	Owner(make_proof_id(i.id, th), t), thm(th), par(nullptr), inner(false) {
	theorem()->proofs.emplace_back(User<Proof>(id()));
	assert(this == theorem()->proofs.back().get());
}

vector<Qed*> Proof::qeds() const {
	vector<Qed*> ret;
	for (const auto& e : elems) {
		if (kind(e) == QED) {
			ret.push_back(qed(e));
		}
	}
	return ret;
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
	for (auto& h : a->hyps) if (h.get()->token.includes(t)) return h.get();
	for (auto& p : a->props) if (p.get()->token.includes(t)) return p.get();
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
	switch (Proof::kind(e)) {
	case Proof::QED: return find(Proof::qed(e), t);
	case Proof::STEP: return find(Proof::step(e), t);
	case Proof::VARS: return find(Proof::vars(e), t);
	default: return nullptr;
	}
}

inline Tokenable* find(Proof* p, const Token& t) {
	if (!p->token.includes(t)) return nullptr;
	for (auto& e : p->elems) {
		if (Tokenable* ret = find(e, t)) {
			return ret;
		}
	}
	return p;
}

inline Tokenable* find(Import* i, const Token& t) {
	return i->token.includes(t) ? i : nullptr;
}

Tokenable* find(Theory::Node& n, const Token& t);

inline Tokenable* find(Theory* th, const Token& t) {
	for (auto& n : th->nodes)
		if (Tokenable* ret = find(n, t)) return ret;
	return nullptr;
}

Tokenable* find(Theory::Node& n, const Token& t) {
	switch (Theory::kind(n)) {
	case Theory::CONST:   if (Tokenable* ret = find(Theory::const_(n), t)) return ret; else return nullptr;
	case Theory::TYPE:    if (Tokenable* ret = find(Theory::type(n), t)) return ret; else return nullptr;
	case Theory::RULE:    if (Tokenable* ret = find(Theory::rule(n), t)) return ret; else return nullptr;
	case Theory::AXIOM:   if (Tokenable* ret = find(Theory::axiom(n), t)) return ret; else return nullptr;
	case Theory::DEF:     if (Tokenable* ret = find(Theory::def(n), t)) return ret; else return nullptr;
	case Theory::THEOREM: if (Tokenable* ret = find(Theory::theorem(n), t)) return ret; else return nullptr;
	case Theory::PROOF:   if (Tokenable* ret = find(Theory::proof(n), t)) return ret; else return nullptr;
	case Theory::THEORY:  if (Tokenable* ret = find(Theory::theory(n), t)) return ret; else return nullptr;
	case Theory::IMPORT:  if (Tokenable* ret = find(Theory::import(n), t)) return ret; else return nullptr;
	case Theory::COMMENT: return nullptr;
	}
	return nullptr;
}

Tokenable* Source::find(const Token& t) {
	return rus::find(&theory, t);
}


}} // mdl::rus

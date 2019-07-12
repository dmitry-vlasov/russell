#include <rus_ast.hpp>

namespace mdl { namespace rus {

inline uint create_id(string pref, string s1, string s2) {
	return Lex::toInt(pref + "_" + s1 + "_" + s2);
}

inline Var create_var(string str, Type* tp) {
	return Var(Lex::toInt(str), tp->id(), Token(tp->token.src()));
}

uint create_super_id(Type* inf, Type* sup) {
	return create_id("sup", show_id(inf->id()), show_id(sup->id()));
}

Rule* create_super(Type* inf, Type* sup) {
	uint id = create_super_id(inf, sup);
	Rule* rule = new Rule(id);
	rule->vars.v.emplace_back(
		Lex::toInt("x"),
		inf->id(),
		Token(inf->token.src())
	);
	rule->term.symbols.push_back(make_unique<Var>(
		Lex::toInt("x"),
		inf->id(),
		Token(inf->token.src())
	));
	rule->term.type.set(sup->id());
	create_rule_term(rule->term, id);
	return rule;
}

static void collect_super_rules(Type* inf, Type* s) {
	for (auto& sup : s->sup) {
		Rule* super = create_super(inf, sup.get());
		inf->supers[sup.get()].reset(super);
		collect_super_rules(inf, sup.get());
	}
}

Type::Type(Id i, const vector<Id>& s, const Token& t) : Owner(i.id(), t) {
	for (auto t : s) {
		sup.emplace_back(t);
	}
	collect_super_rules(this, this);
}

inline uint make_proof_id(uint id, Id th) {
	if (id == -1) {
		const string& th_name = (th.id() == -1) ? "anonymous" : Lex::toStr(th.id());
		static cmap<uint, uint> proof_indexes;

		typename cmap<uint, uint>::accessor a;
		uint ind = proof_indexes.find(a, th.id()) ? a->second + 1 : 0;
		proof_indexes.insert(a, th.id());
		a->second = ind;
		return Lex::toInt(string("_proof_of_") + th_name + "_" + to_string(ind));
	} else {
		return id;
	}
}

inline void check_disjointed(const set<uint>& s1, const set<uint>& s2) {
	if (s1.size() > s2.size()) return check_disjointed(s2, s1);
	for (uint x : s1) {
		if (s2.find(x) != s2.end()) {
			throw Error("disjointed variable restriction violation", Lex::toStr(x));
		}
	}
}

void Disj::check(const Substitution& s, Assertion* t) const {
	for (const auto& p : dvars) {
		if (!s.maps(p.v) || !s.maps(p.w)) continue;
		set<uint> v1_vars = s.map(p.v)->vars();
		set<uint> v2_vars = s.map(p.w)->vars();
		check_disjointed(v1_vars, v2_vars);
		if (t) {
			t->disj.make_pairs_disjointed(v1_vars, v2_vars);
		}
	}
}

void Disj::make_pairs_disjointed(const set<uint>& vars1, const set<uint>& vars2) {
	if (vars1.empty() || vars2.empty()) return;
	for (uint v1 : vars1) {
		for (uint v2 : vars2) {
			if (v1 != v2) {
				dvars.emplace(v1, v2);
			}
		}
	}
}

Disj::Disj(const Vector& vect, const Token& t) : WithToken(t) {
	for (const auto& dis : vect) {
		const set<uint>& d = *dis.get();
		for (auto v : d) {
			for (auto w : d) {
				if (v != w) {
					dvars.emplace(v, w);
				}
			}
		}
	}
}

static void addPair(const set<Disj::Pair>& dmap, Disj::Vector& d, uint v1, uint v2) {

	auto try_to_extend = [&dmap](set<uint>* dis, uint v1, uint v2) {
		if (dis->find(v1) == dis->end()) return false;
		for (uint d : *dis) {
			if (dmap.find(Disj::Pair(d, v2)) == dmap.end()) {
				return false;
			}
		}
		dis->insert(v2);
		return true;
	};

	for (auto& d : d) {
		auto dis = d.get();
		if (dis->count(v1) && dis->count(v2)) return;
		if (try_to_extend(dis, v1, v2)) return;
		if (try_to_extend(dis, v2, v1)) return;
	}
	d.emplace_back(new set<uint>());
	d.back()->insert(v1);
	d.back()->insert(v2);
}

Disj::Vector Disj::toVector() const {
	Vector v;
	for (const auto& p : dvars) {
		addPair(dvars, v, p.v, p.w);
	}
	return v;
}

Proof::Proof(Theorem* th, const Token& t) :
	WithToken(t), theorem(th), par(nullptr), inner(false) {
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

static AbstProof::Node* abstProof(const Step* step) {
	AbstProof::Node* ret = new AbstProof::Node(step->ass_id(), step->refs.size());
	for (uint i = 0; i < step->refs.size(); ++i) {
		if (const Step* ch = step->refs[i]->step()) {
			ret->setChild(i, abstProof(ch));
		}
	}
	return ret;
}

AbstProof Proof::abst() const {
	vector<Qed*> qs = qeds();
	if (!qs.size()) {
		throw Error("no qeds in a proof");
	}
	return abstProof(qeds().at(0)->step);
}

static void complete_expr_vars(const Expr& expr, Vars& vars, std::function<bool(uint)> decled_somewehre_else = [](uint) { return false; }) {
	for (auto& s : expr.symbols) {
		if (const Var* v = dynamic_cast<const Var*>(s.get())) {
			if (!vars.isDeclared(v->lit()) && !decled_somewehre_else(v->lit())) {
				vars.v.emplace_back(*v);
			}
		}
	}
}

void complete_assertion_vars(Assertion* a) {
	for (auto& h : a->hyps) {
		complete_expr_vars(h->expr, a->vars);
	}
	complete_expr_vars(a->prop->expr, a->vars);
}

void complete_proof_vars(Proof* proof) {
	for (auto& e : proof->elems) {
		if (rus::Step* step = rus::Proof::step(e)) {
			complete_expr_vars(
				step->expr,
				proof->vars,
				[proof](uint l) { return proof->theorem->vars.isDeclared(l); }
			);
		}
	}
}

/*
inline Token* find(Constant* c, const Token& t) {
	return c->token.includes(t) ? &c->token : nullptr;
}

inline Token* find(Type* tp, const Token& t) {
	return tp->token.includes(t) ? tp-> : nullptr;
}

inline Token* find(Rule* r, const Token& t) {
	if (r->token.includes(t)) return nullptr;
	if (r->vars.token.includes(t)) return &r->vars;
	if (r->term.token.includes(t)) return &r->term;
	return r;
}

inline Token* find(Assertion* a, const Token& t) {
	if (!a->token.includes(t)) return nullptr;
	if (a->vars.token.includes(t)) return &a->vars;
	if (a->disj.token.includes(t)) return &a->disj;
	for (auto& h : a->hyps) if (h.get()->token.includes(t)) return h.get();
	for (auto& p : a->props) if (p.get()->token.includes(t)) return p.get();
	return a;
}

inline Token* find(Def* d, const Token& t) {
	if (!d->token.includes(t)) return nullptr;
	if (d->dfm.token.includes(t)) return &d->dfm;
	if (d->dfs.token.includes(t)) return &d->dfs;
	if (d->prop.token.includes(t)) return &d->prop;
	return find(static_cast<Assertion*>(d), t);
}

inline Token* find(Qed* q, const Token& t) {
	return q->token.includes(t) ? q : nullptr;
}

inline Token* find(Step* s, const Token& t) {
	return s->token.includes(t) ? s : nullptr;
}

inline Token* find(Vars* v, const Token& t) {
	return v->token.includes(t) ? v : nullptr;
}

inline Token* find(Proof::Elem& e, const Token& t) {
	switch (Proof::kind(e)) {
	case Proof::QED: return find(Proof::qed(e), t);
	case Proof::STEP: return find(Proof::step(e), t);
	case Proof::VARS: return find(Proof::vars(e), t);
	default: return nullptr;
	}
}

inline Token* find(Proof* p, const Token& t) {
	if (!p->token.includes(t)) return nullptr;
	for (auto& e : p->elems) {
		if (Token* ret = find(e, t)) {
			return ret;
		}
	}
	return p;
}

inline Token* find(Import* i, const Token& t) {
	return i->token.includes(t) ? i : nullptr;
}

Token* find(Theory::Node& n, const Token& t);

inline Token* find(Theory* th, const Token& t) {
	for (auto& n : th->nodes)
		if (Token* ret = find(n, t)) return ret;
	return nullptr;
}

Token* find(Theory::Node& n, const Token& t) {
	switch (Theory::kind(n)) {
	case Theory::CONSTANT: if (Token* ret = find(Theory::constant(n), t)) return ret; else return nullptr;
	case Theory::TYPE:     if (Token* ret = find(Theory::type(n), t)) return ret; else return nullptr;
	case Theory::RULE:     if (Token* ret = find(Theory::rule(n), t)) return ret; else return nullptr;
	case Theory::AXIOM:    if (Token* ret = find(Theory::axiom(n), t)) return ret; else return nullptr;
	case Theory::DEF:      if (Token* ret = find(Theory::def(n), t)) return ret; else return nullptr;
	case Theory::THEOREM:  if (Token* ret = find(Theory::theorem(n), t)) return ret; else return nullptr;
	case Theory::PROOF:    if (Token* ret = find(Theory::proof(n), t)) return ret; else return nullptr;
	case Theory::THEORY:   if (Token* ret = find(Theory::theory(n), t)) return ret; else return nullptr;
	case Theory::IMPORT:   if (Token* ret = find(Theory::import(n), t)) return ret; else return nullptr;
	case Theory::COMMENT: return nullptr;
	}
	return nullptr;
}

Token* Source::find(const Token& t) {
	return rus::find(&theory, t);
}
*/

}} // mdl::rus

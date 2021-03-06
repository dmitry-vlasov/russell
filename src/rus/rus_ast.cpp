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
	Rule* rule = new Rule(id, inf->token);
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
			throw Error("disjointed variable restriction violation, common var", Lex::toStr(x));
		}
	}
}

void Disj::check(const Substitution& s, Disj* outer) const {
	for (const auto& p : dvars) {
		/*if (!s.maps(p.v) || !s.maps(p.w)) {
			string err;
			err += "this disj: " + show() + "\n";
			err += "outer: " + (outer ? outer->show() : "") + "\n";
			err += "pair: " + Lex::toStr(p.v) + " " + Lex::toStr(p.w) + "\n";
			err += "sub:\n" + s.show() + "\n";
			throw Error(err);
			continue;
		}*/
		//if (!s.maps(p.v) || !s.maps(p.w)) continue;
		set<uint> v1_vars = s.maps(p.v) ? s.map(p.v)->vars() : set<uint>({p.v});
		set<uint> v2_vars = s.maps(p.w) ? s.map(p.w)->vars() : set<uint>({p.w});
		try {
			check_disjointed(v1_vars, v2_vars);
		} catch (Error& err) {
			err.msg += "disjointed pair: " + Lex::toStr(p.v) + " and " + Lex::toStr(p.w) + "\n";
			throw err;
		}
		if (outer) {
			outer->make_pairs_disjointed(v1_vars, v2_vars);
		}
	}
}

void Disj::make_pairs_disjointed(const set<uint>& vars1, const set<uint>& vars2) {
	for (uint v1 : vars1) {
		for (uint v2 : vars2) {
			if (v1 != v2) {
				dvars.emplace(v1, v2);
			}
		}
	}
}

bool debug_check_disj = false;

inline bool disjointed_are_satisfied(const set<uint>& s1, const set<uint>& s2) {
	if (s1.size() > s2.size()) return disjointed_are_satisfied(s2, s1);
	for (uint x : s1) {
		if (s2.find(x) != s2.end()) {
			if (debug_check_disj) {
				cout << "s2.find(x) != s2.end(): " << Lex::toStr(x) << endl;
			}
			return false;
		}
	}
	return true;
}

bool Disj::satisfies(const Substitution& s, const Disj* outer) const {
	for (const auto& p : dvars) {
		set<uint> v1_vars = s.maps(p.v) ? s.map(p.v)->vars() : set<uint>({p.v});
		set<uint> v2_vars = s.maps(p.w) ? s.map(p.w)->vars() : set<uint>({p.w});
		if (!disjointed_are_satisfied(v1_vars, v2_vars)) {

			if (debug_check_disj) {
				cout << "AAA" << endl;
				cout << "v1_vars: {";
				for (uint v : v1_vars) {
					cout << Lex::toStr(v) << ", ";
				}
				cout << "}" << endl;
				cout << "v2_vars: {";
				for (uint v : v2_vars) {
					cout << Lex::toStr(v) << ", ";
				}
				cout << "}" << endl;
				cout << "s:" << endl << s << endl;
			}

			return false;
		}
		if (outer && !outer->check_pairs_disjointed(v1_vars, v2_vars)) {

			if (debug_check_disj) {
				cout << "BBB" << endl;
				cout << "v1_vars: {";
				for (uint v : v1_vars) {
					cout << Lex::toStr(v) << ", ";
				}
				cout << "}" << endl;
				cout << "v2_vars: {";
				for (uint v : v2_vars) {
					cout << Lex::toStr(v) << ", ";
				}
				cout << "}" << endl;
				cout << "outer:" << endl << *outer << endl;
			}

			return false;
		}
	}
	return true;
}

bool Disj::check_pairs_disjointed(const set<uint>& vars1, const set<uint>& vars2) const {
	for (uint v1 : vars1) {
		for (uint v2 : vars2) {
			if (v1 != v2) {
				if (!dvars.count(Pair(v1, v2))) {

					if (debug_check_disj) {
						cout << "!dvars.count(Pair(v1, v2)): " << Lex::toStr(v1) << " " << Lex::toStr(v2)  << endl;
					}

					return false;
				}
			}
		}
	}
	return true;
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

void traverseProof(Step* step, std::function<void(Writable*)> f) {
	f(step);
	for (auto& ref : step->refs) {
		if (ref->step()) {
			traverseProof(ref->step(), f);
		} else if (ref->hyp()) {
			f(ref->hyp());
		}
	}
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
	return abstProof(qed());
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
	a->vars.v.clear();
	for (auto& h : a->hyps) {
		complete_expr_vars(h->expr, a->vars);
	}
	complete_expr_vars(a->prop->expr, a->vars);
}

void complete_proof_vars(Proof* proof) {
	proof->vars.v.clear();
	for (auto& step : proof->steps) {
		complete_expr_vars(
			step->expr,
			proof->vars,
			[proof](uint l) { return proof->theorem->vars.isDeclared(l); }
		);
	}
}

void Theory::insert(Writable* w, uint pos) {
	if (!w) {
		throw Error("at insert: nullptr");
	}
	if (pos > nodes.size()) {
		throw Error("at insert: theory size " + to_string(nodes.size()) + " < " + to_string(pos));
	}
	Token token_prime = pos < nodes.size() ? getWithToken(nodes.at(pos))->token : Token(token.src());
	if (Constant* c = dynamic_cast<Constant*>(w)) {
		nodes.emplace(nodes.begin() + pos, unique_ptr<Constant>(c));
	} else if (Type* t = dynamic_cast<Type*>(w)) {
		nodes.emplace(nodes.begin() + pos, unique_ptr<Type>(t));
	} else if (Rule* r = dynamic_cast<Rule*>(w)) {
		nodes.emplace(nodes.begin() + pos, unique_ptr<Rule>(r));
	} else if (Axiom* a = dynamic_cast<Axiom*>(w)) {
		nodes.emplace(nodes.begin() + pos, unique_ptr<Axiom>(a));
	} else if (Def* d = dynamic_cast<Def*>(w)) {
		nodes.emplace(nodes.begin() + pos, unique_ptr<Def>(d));
	} else if (Theorem* t = dynamic_cast<Theorem*>(w)) {
		nodes.emplace(nodes.begin() + pos, unique_ptr<Theorem>(t));
	} else if (Theory* t = dynamic_cast<Theory*>(w)) {
		nodes.emplace(nodes.begin() + pos, unique_ptr<Theory>(t));
	} else if (Comment* c = dynamic_cast<Comment*>(w)) {
		nodes.emplace(nodes.begin() + pos, unique_ptr<Comment>(c));
	} else {
		throw Error("unknown kind of theory contents: " + w->show());
	}
	getWithToken(nodes.at(pos))->token = token_prime;
}

Writable* Theory::getWritable(const Node& n) {
	switch (kind(n)) {
	case CONSTANT: return constant(n);
	case TYPE:     return type(n);
	case RULE:     return rule(n);
	case AXIOM:    return axiom(n);
	case DEF:      return def(n);
	case THEOREM:  return theorem(n);
	case THEORY:   return theory(n);
	case COMMENT:  return comment(n);
	default: throw Error("unknown kind of theory contents");
	}
}

WithToken* Theory::getWithToken(const Node& n) {
	switch (kind(n)) {
	case CONSTANT: return constant(n);
	case TYPE:     return type(n);
	case RULE:     return rule(n);
	case AXIOM:    return axiom(n);
	case DEF:      return def(n);
	case THEOREM:  return theorem(n);
	case THEORY:   return theory(n);
	case COMMENT:  return comment(n);
	default: throw Error("unknown kind of theory contents");
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

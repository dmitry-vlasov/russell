#include "smm/tree.hpp"
#include "rus/ast.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm {

extern map<uint, rus::Const> math_symb;

namespace {

struct State {
	Map<const Assertion*, rus::Axiom*>   axioms;
	Map<const Assertion*, rus::Theorem*> theorems;
	Map<const Assertion*, rus::Def*>     defs;
	Map<const rus::Rule*, rus::Node*>    rules;
	Map<const Source*,    rus::Source*>  sources;
	Map<Symbol, rus::Type*> types;
	rus::Type*    type_wff;
	rus::Type*    type_set;
	rus::Type*    type_class;
	Set<Symbol>   redundant_consts;
	Set<rus::Symbol> constants;
	rus::Theory*  theory;
	uint ind;
};

inline rus::Symbol translate_symb(Symbol s, rus::Type* t = nullptr) {
	auto p = math_symb.find(s.lit);
	if (p == math_symb.end() || t)
		return rus::Symbol(s, t);
	else {
		rus::Symbol rs = (*p).second.symb;
		rs.type = t;
		return rs;
	}
}

rus::Expr translate_expr(const Expr& ex, const State& state, const Assertion* ass) {
	rus::Expr e;
	for (auto it = ex.symbols.begin(); it != ex.symbols.end(); ++ it) {
		// pass the first symbol
		if (it == ex.symbols.begin())
			continue;
		rus::Type* t = nullptr;
		for (auto f : ass->floating)
			if (f->var() == *it) {
				assert(state.types.has(f->type()));
				t = state.types.m.find(f->type())->second;
				break;
			}
		for (auto i : ass->inner)
			if (i->var() == *it) {
				assert(state.types.has(i->type()));
				t = state.types.m.find(i->type())->second;
				break;
			}
		e.push_back(translate_symb(*it, t));
	}
	// it's the best what we can do here ...
	e.type = state.type_wff;
	return e;
}

void translate_const(const Constants* consts, State& state) {
	for (auto s : consts->expr.symbols) {
		if (state.redundant_consts.has(s))
			continue;
		rus::Const* c = nullptr;
		auto p = math_symb.find(s.lit);
		if (p == math_symb.end())
			c = new rus::Const{state.ind ++, rus::Symbol(s), rus::Symbol(), rus::Symbol()};
		else {
			rus::Const& rc = (*p).second;
			c = new rus::Const{state.ind ++ , rc.symb, rc.ascii, rc.latex};
		}

		if (state.constants.has(c->symb))
			delete c;
		else {
			state.constants.s.insert(c->symb);
			state.theory->nodes.push_back(rus::Node(c));
		}
	}
}

inline bool is_turnstile(Symbol s) {
	Symbol t(Smm::mod().lex.symbols.toInt("|-"));
	return s == t;
}

rus::Type* translate_type(Symbol type_sy, State& state);

template<typename T>
rus::Vars translate_vars(vector<T*> decls, State& state) {
	rus::Vars rus_vars;
	for (auto flo : decls) {
		rus::Type* type = translate_type(flo->type(), state);
		rus_vars.v.push_back(rus::Symbol(flo->var(), type, true));
	}
	return rus_vars;
}

rus::Disj translate_disj(const Assertion* ass, State& state) {
	rus::Disj rus_disj;
	for (auto dis : ass->disjointed) {
		rus_disj.d.push_back(vector<rus::Symbol>());
		vector<rus::Symbol>& rus_dis = rus_disj.d.back();
		for (auto v : dis->expr.symbols) {
			rus::Type* type = nullptr;
			for (auto flo : ass->floating) {
				if (flo->var() == v) type = translate_type(flo->type(), state);
			}
			rus::Symbol rv = rus::Symbol(v.lit, type, true);
			rus_dis.push_back(rv);
		}
	}
	return rus_disj;
}

rus::Type* translate_type(Symbol type_sy, State& state) {
	if (state.types.has(type_sy))
		return state.types.m.find(type_sy)->second;
	else {
		string type_str = Smm::get().lex.symbols.toStr(type_sy.lit);
		uint type_id = Smm::mod().lex.labels.toInt(type_str);
		rus::Type* type = new rus::Type { state.ind ++, type_id };
		state.types[type_sy] = type;
		state.theory->nodes.push_back(type);
		if (type_str == "wff") state.type_wff = type;
		if (type_str == "set") state.type_set = type;
		if (type_str == "class") state.type_class = type;
		return type;
	}
}

inline bool rule_term_is_super(const Expr& term) {
	return term.symbols.size() == 2 && !term.symbols[0].var && term.symbols[1].var;
}

vector<rus::Node>::iterator type_index(const rus::Type* type, State& state) {
	for (auto it = state.theory->nodes.begin(); it != state.theory->nodes.end(); ++ it) {
		if (it->kind == rus::Node::TYPE && type == it->val.tp)
			return it;
	}
	return state.theory->nodes.end();
}

void translate_super(const Assertion* ass, State& state) {
	Symbol super_sy = ass->prop.expr[0];
	Symbol infer_sy = ass->floating[0]->type();
	assert(ass->prop.expr[1] == ass->floating[0]->var());
	rus::Type* super = translate_type(super_sy, state);
	rus::Type* infer = translate_type(infer_sy, state);
	infer->sup.push_back(super);
	auto sup_it = type_index(super, state);
	auto inf_it = type_index(infer, state);
	if (sup_it > inf_it) {
		state.theory->nodes.erase(sup_it);
		state.theory->nodes.insert(inf_it, super);
	}
}

inline bool super_type(const rus::Type* t1, const rus::Type* t2) {
	if (t1 == t2) return true;
	for (auto s : t1->sup)
		if (t2 == s)
			return true;
	return false;

}

bool less_general(const rus::Rule* r1, const rus::Rule* r2) {
	if (!super_type(r2->type, r1->type))
		return false;
	const rus::Expr::Node *n = r1->term.first;
	const rus::Expr::Node *m = r2->term.first;
	while (n && m) {
		if (!n->symb.type && !m->symb.type) {
			if (n->symb != m->symb)
				return false;
		} else if (n->symb.type && m->symb.type) {
			if (!super_type(n->symb.type, m->symb.type))
				return false;
		} else {
			return false;
		}
		n = n->next;
		m = m->next;
	}
	return n == m;
}

void translate_rule(const Assertion* ass, State& state) {
	if (rule_term_is_super(ass->prop.expr)) {
		translate_super(ass, state);
		return;
	}
	rus::Rule* rule = new rus::Rule {
		state.ind ++,
		ass->prop.label,
		translate_type(ass->prop.expr[0], state),
		translate_vars(ass->floating, state),
		translate_expr(ass->prop.expr, state, ass)
	};
	for (auto p : state.rules.m) {
		bool less_gen = less_general(p.first, rule);
		bool more_gen = less_general(rule, p.first);
		if (less_gen && !more_gen) {
			delete p.second->val.rul;
			p.second->val.rul = rule;
			return;
		} else if (more_gen) {
			delete rule;
			return;
		}
	}
	state.theory->nodes.push_back(rule);
	state.rules[rule] = &state.theory->nodes.back();
}

template<class T>
void translate_assertion(const Assertion* ass, T* a, State& state) {
	a->ass.id = ass->prop.label;
	a->ass.vars = translate_vars(ass->floating, state);
	a->ass.disj = translate_disj(ass, state);
	uint hc = 0;
	for (auto ess : ass->essential) {
		rus::Expr ex = translate_expr(ess->expr, state, ass);
		a->ass.hyps.push_back(new rus::Hyp{hc++, ex});
	}
	rus::Expr ex = translate_expr(ass->prop.expr, state, ass);
	a->ass.props.push_back(new rus::Prop{0, ex});
}

void translate_axiom(const Assertion* ass, State& state) {
	rus::Axiom* ax = new rus::Axiom;
	ax->ass.ind = state.ind ++;
	translate_assertion<rus::Axiom>(ass, ax, state);
	state.theory->nodes.push_back(ax);
	state.axioms[ass] = ax;
}


inline Symbol open_brace() { Symbol s(Smm::mod().lex.symbols.toInt("{")); return s; }
inline Symbol close_brace() {Symbol s(Smm::mod().lex.symbols.toInt("}")); return s; }
inline Symbol open_brack() { Symbol s(Smm::mod().lex.symbols.toInt("(")); return s; }
inline Symbol close_brack() { Symbol s(Smm::mod().lex.symbols.toInt(")")); return s; }
inline Symbol eqty() { Symbol s(Smm::mod().lex.symbols.toInt("=")); return s; }
inline Symbol eqiv() { Symbol s(Smm::mod().lex.symbols.toInt("<->")); return s; }
inline Symbol dfm() { Symbol s(Smm::mod().lex.symbols.toInt("defiendum")); return s; }
inline Symbol dfs() { Symbol s(Smm::mod().lex.symbols.toInt("definiens")); return s; }

inline void count_br(Symbol s, uint& brack_depth, uint& brace_depth) {
	if (s == open_brace())  ++ brace_depth;
	if (s == close_brace()) -- brace_depth;
	if (s == open_brack())  ++ brack_depth;
	if (s == close_brack()) -- brack_depth;
}
inline bool low_depth(uint brack_depth, uint brace_depth) {
	return
		(brack_depth <= 1 && brace_depth == 0) ||
		(brack_depth == 0 && brace_depth <= 1);
}

vector<Symbol>::const_iterator eq_position(const Expr& ex) {
	uint brack_depth = 0;
	uint brace_depth = 0;
	for (auto it = ex.symbols.begin() + 1; it != ex.symbols.end(); ++ it) {
		count_br(*it, brack_depth, brace_depth);
		if (*it == eqiv() && low_depth(brack_depth, brace_depth)) return it;
	}
	brack_depth = 0;
	brace_depth = 0;
	for (auto it = ex.symbols.begin() + 1; it != ex.symbols.end(); ++ it) {
		count_br(*it, brack_depth, brace_depth);
		if (*it == eqty() && low_depth(brack_depth, brace_depth)) return it;
	}
	return ex.symbols.end();
}

void translate_def(const Assertion* ass, State& state) {
	rus::Def* def = new rus::Def;
	def->ass.ind = state.ind ++;
	translate_assertion<rus::Def>(ass, def, state);
	const Expr& ex = ass->prop.expr;
	auto eq_pos = eq_position(ex);

	auto dfm_beg = ex.symbols.begin() + 1;
	auto dfm_end = eq_pos;
	auto dfs_beg = eq_pos + 1;
	auto dfs_end = ex.symbols.end();

	if (*eq_pos == eqiv()) {
		++ dfm_beg;
		-- dfs_end;
		def->dfm.type = state.type_wff;
		def->dfs.type = state.type_wff;
	} else {
		def->dfm.type = state.type_class;
		def->dfs.type = state.type_class;
	}
	def->prop.type = state.type_wff;
	for (auto it = ex.symbols.begin() + 1; it != ex.symbols.end(); ++ it) {
		if ((dfm_beg <= it) && (it < dfm_end)) {
			if (dfm_beg == it)
				def->prop.push_back(dfm());
			def->dfm.push_back(translate_symb(*it));
		} else if ((dfs_beg <= it) && (it < dfs_end)) {
			if (dfs_beg == it)
				def->prop.push_back(dfs());
			def->dfs.push_back(translate_symb(*it));
		} else {
			def->prop.push_back(translate_symb(*it));
		}
	}
	state.theory->nodes.push_back(def);
	state.defs[ass] = def;
}

bool is_def(const Assertion* ass) {
	if (Smm::get().lex.labels.toStr(ass->prop.label).substr(0,3) != "df-") return false;
	const Expr& ex = ass->prop.expr;
	auto eq_pos = eq_position(ex);
	return eq_pos != ex.symbols.end();
}

rus::Node::Kind ass_kind(const Assertion* ass) {
	if (!is_turnstile(ass->prop.expr.symbols.front())) {
		return rus::Node::RULE;
	} else if (is_def(ass)) {
		return rus::Node::DEF;
	} else if (!ass->proof) {
		return rus::Node::AXIOM;
	} else {
		return rus::Node::THEOREM;
	}
}

rus::Proof::Elem translate_step(Ref ref, rus::Proof* proof, rus::Theorem* thm, State& state, const Assertion* a) {
	assert(ref.type == Ref::PROOF);
	vector<rus::Proof::Elem>& elems = proof->elems;
	rus::Proof::Elem el(new rus::Step(proof));
	Assertion* ass = ref.val.prf->refs.back().val.ass;
	for (uint i = 0; i < ass->essential.size(); ++ i) {
		Ref r = ref.val.prf->refs[i];
		assert(r.type == Ref::ESSENTIAL || r.type == Ref::PROOF);
		rus::Ref hr;
		if (r.type == Ref::ESSENTIAL) {
			hr = rus::Ref(thm->ass.hyps[r.index()]);
		} else {
			hr = rus::Ref(translate_step(r, proof, thm, state, a).val.step);
		}
		el.val.step->refs.push_back(hr);
	}
	el.val.step->ind = elems.size();
	el.val.step->expr = translate_expr(ref.expr, state, a);
	switch (ass_kind(ass)) {
	case rus::Node::AXIOM:
		el.val.step->val.axm = state.axioms.m.find(ass)->second;
		el.val.step->kind = rus::Step::AXM; break;
	case rus::Node::DEF:
		el.val.step->val.def = state.defs.m.find(ass)->second;
		el.val.step->kind = rus::Step::DEF; break;
	case rus::Node::THEOREM:
		el.val.step->val.thm = state.theorems.m.find(ass)->second;
		el.val.step->kind = rus::Step::THM; break;
	default : assert(false && "impossible"); break;
	}
	elems.push_back(el);
	return el;
}

void translate_proof(const Assertion* ass, rus::Theorem* thm, State& state) {
	Ref tree = Ref(to_tree(ass->proof));
	eval(tree);
	rus::Proof* p = new rus::Proof();
	p->ind = state.ind ++;
	p->vars = translate_vars(ass->inner, state);
	p->thm = thm;
	translate_step(tree, p, thm, state, ass);
	rus::Prop* pr = thm->ass.props.front();
	rus::Step* st = p->elems.back().val.step;
	p->elems.push_back(new rus::Qed{pr, st});
	state.theory->nodes.push_back(p);
	tree.destroy();
}

void translate_theorem(const Assertion* ass, State& state) {
	rus::Theorem* thm = new rus::Theorem;
	thm->ass.ind = state.ind ++;
	translate_assertion<rus::Theorem>(ass, thm, state);
	state.theory->nodes.push_back(thm);
	translate_proof(ass, thm, state);
	state.theorems[ass] = thm;
}

void translate_ass(const Assertion* ass, State& state) {
	switch (ass_kind(ass)) {
	case rus::Node::RULE    : translate_rule(ass, state);    break;
	case rus::Node::DEF     : translate_def(ass, state);     break;
	case rus::Node::AXIOM   : translate_axiom(ass, state);   break;
	case rus::Node::THEOREM : translate_theorem(ass, state); break;
	default : assert(false && "impossible"); break;
	}
}

rus::Source* translate_source(const Source* source, State& state, rus::Source* target = nullptr);

inline rus::Import* translate_import(const Inclusion* inc, State& s) {
	rus::Source* src = translate_source(inc->source, s);
	return new rus::Import(src, inc->primary);
}

void translate_theory(const Source* source, State& state) {
	for (auto node : source->contents) {
		if (node.type == Node::INCLUSION) {
			rus::Import* imp = translate_import(node.val.inc, state);
			state.theory->nodes.push_back(imp);
		}
	}
	for (auto node : source->contents) {
		switch (node.type) {
		case Node::CONSTANTS: translate_const(node.val.cst, state); break;
		case Node::ASSERTION: translate_ass(node.val.ass, state); break;
		default : assert(false && "impossible"); break;
		}
	}
}

rus::Source* translate_source(const Source* src, State& state, rus::Source* target) {
	if (state.sources.has(src)) {
		return state.sources[src];
	} else {
		Config conf = Smm::get().config;
		if (!target) {
			target = new rus::Source(
				conf.deep ? conf.out : conf.root,
				src->name
			);
			target->theory = new rus::Theory();
		}
		state.sources[src] = target;
		state.theory = target->theory;
		translate_theory(src, state);
		return target;
	}
}

} // anonymous namespace

rus::Source* translate_to_rus(const Source* source) {
	Config conf = Smm::get().config;
	rus::Source* target = new rus::Source(
		conf.deep ? conf.out : conf.root,
		conf.deep ? conf.in  : conf.out
	);
	target->theory = new rus::Theory();
	State state;
	state.ind = 0;
	state.type_wff = nullptr;
	state.type_set = nullptr;
	state.type_class = nullptr;
	state.redundant_consts.s.insert(Smm::get().lex.symbols.getInt("wff"));
	state.redundant_consts.s.insert(Smm::get().lex.symbols.getInt("set"));
	state.redundant_consts.s.insert(Smm::get().lex.symbols.getInt("class"));
	state.redundant_consts.s.insert(Smm::get().lex.symbols.getInt("|-"));
	translate_source(source, state, target);
	return target;
}

}} // mdl::smm

#include "rus_ast.hpp"
#include "mm_sys.hpp"
#include "mm_math_symb.hpp"
#include "mm_tree.hpp"

namespace mdl { namespace mm { namespace {

struct Maps {
	map<const mm::Source*,rus::Source*> sources;
	map<uint, deque<rus::Type*>> type_defs;
	map<uint, rus::Type*> types;
	map<uint, rus::Rule*> rules;
	map<uint, mm::Ref*> redundant_assertions;
	stack<rus::Theory*>  theory;
};

inline uint open_brace()  { static uint ret = Lex::toInt("{"); return ret; }
inline uint close_brace() { static uint ret = Lex::toInt("}"); return ret; }
inline uint open_brack()  { static uint ret = Lex::toInt("("); return ret; }
inline uint close_brack() { static uint ret = Lex::toInt(")"); return ret; }
inline uint turnstile()   { static uint ret = Lex::toInt("|-"); return ret; }
inline uint eqty() { static uint ret = Lex::toInt("="); return ret; }
inline uint eqiv() { static uint ret = Lex::toInt("<->"); return ret; }
inline uint dfm()  { static uint ret = Lex::toInt("defiendum"); return ret; }
inline uint dfs()  { static uint ret = Lex::toInt("definiens"); return ret; }
inline uint wff()  { static uint ret = Lex::toInt("wff"); return ret; }
inline uint clas() { static uint ret = Lex::toInt("class"); return ret; }

inline rus::Symbol translate_const(uint s) {
	auto p = math_consts().find(s);
	if (p == math_consts().end()) {
		return rus::Symbol(s, s, rus::Symbol::CONST);
	} else {
		return rus::Symbol((*p).second.symb, s, rus::Symbol::CONST);
	}
}

inline rus::Symbol translate_var(uint symb, uint type) {
	auto p = math_vars().find(symb);
	if (p == math_vars().end()) {
		return rus::Symbol(symb, type, rus::Symbol::VAR);
	} else {
		return rus::Symbol((*p).second.var, type, rus::Symbol::VAR);
	}
}

inline uint translate_var_type(uint v, const Assertion* ass) {
	for (const auto& f : ass->outerVars) {
		if (f.get()->var() == v) {
			return f.get()->type();
		}
	}
	for (const auto& i : ass->innerVars) {
		if (i.get()->var() == v) {
			return i.get()->type();
		}
	}
	throw Error("no type is given for variable", Lex::toStr(v));
	return -1;
}

inline rus::Symbol translate_symb(Symbol s, const Assertion* ass) {
	if (s.var) {
		return translate_var(s.lit, translate_var_type(s.lit, ass));
	} else {
		return translate_const(s.lit);
	}
}

rus::Expr translate_expr(const Expr& ex, const Assertion* ass) {
	rus::Expr e;
	e.symbols.reserve(ex.size() - 1);
	for (auto it = ex.begin(); it != ex.end(); ++ it) {
		// pass the first symbol
		if (it == ex.begin()) continue;
		uint s = it->lit;
		if (it->var) {
			uint type = translate_var_type(s, ass);
			auto p = math_vars().find(s);
			if (p == math_vars().end()) {
				e.symbols.emplace_back(s, type, rus::Symbol::VAR);
			} else {
				e.symbols.emplace_back((*p).second.var, type, rus::Symbol::VAR);
			}
		} else {
			auto p = math_consts().find(s);
			if (p == math_consts().end()) {
				e.symbols.emplace_back(s, s, rus::Symbol::CONST);
			} else {
				e.symbols.emplace_back((*p).second.symb, s, rus::Symbol::CONST);
			}
		}
	}
	// it's the best what we can do here ...
	e.type.set(wff());
	return e;
}

void translate_constant(const Const* constant, Maps& state) {
	uint s = constant->symb;
	auto t = state.type_defs.find(s);
	if (t == state.type_defs.end()) {
		if (s != turnstile()) {
			rus::Const* c = nullptr;
			auto p = math_consts().find(s);
			if (p == math_consts().end()) {
				c = new rus::Const(s, rus::Symbol::undef(), rus::Symbol::undef());
			} else {
				c = new rus::Const(p->second.symb, p->second.ascii, p->second.latex);
			}
			state.theory.top()->nodes.emplace_back(unique_ptr<rus::Const>(c));
		}
	} else {
		for (rus::Type* type : t->second) {
			state.theory.top()->nodes.emplace_back(unique_ptr<rus::Type>(type));
		}
	}
}

template<typename T>
rus::Vars translate_vars(const vector<T>& decls) {
	rus::Vars rus_vars;
	for (const auto& flo : decls) {
		rus_vars.v.push_back(translate_var(flo.get()->var(), flo.get()->type()));
	}
	return rus_vars;
}

rus::Disj translate_disj(const Assertion* ass) {
	rus::Disj rus_disj;
	for (const auto& dis : ass->disj.vect) {
		rus_disj.d.push_back(vector<rus::Symbol>());
		vector<rus::Symbol>& rus_dis = rus_disj.d.back();
		rus_dis.reserve(dis.get()->size());
		for (auto v : *dis.get()) {
			uint type = translate_var_type(v, ass);
			rus_dis.push_back(translate_var(v, type));
		}
	}
	return rus_disj;
}

rus::Type* translate_type(uint t, Maps& state) {
	auto it = state.types.find(t);
	if (it != state.types.end()) {
		return it->second;
	} else {
		rus::Type* type = new rus::Type(t);
		state.types[t] = type;
		state.type_defs[t].push_back(type);
		return type;
	}
}

inline bool super_type(const rus::Type* t1, const rus::Type* t2) {
	if (t1 == t2) {
		return true;
	} else {
		for (auto& s : t1->sup) {
			if (t2 == s) {
				return true;
			}
		}
		return false;
	}
}

bool less_general(const rus::Rule* r1, const rus::Rule* r2) {
	if (!super_type(r2->term.type.get(), r1->term.type.get())) {
		return false;
	}
	auto n = r1->term.symbols.begin();
	auto n_end = r1->term.symbols.end();
	auto m = r2->term.symbols.begin();
	auto m_end = r2->term.symbols.end();
	while (n != n_end && m != m_end) {
		if (!n->type() && !m->type()) {
			if (*n != *m) {
				return false;
			}
		} else if (n->type() && m->type()) {
			if (!super_type(n->type(), m->type())) {
				return false;
			}
		} else {
			return false;
		}
		++ n; ++ m;
	}
	return n == n_end && m == m_end;
}

void translate_rule(const Assertion* ass, Maps& state) {
	auto it = state.rules.find(ass->id());
	if (it != state.rules.end()) {
		rus::Rule* rule = it->second;
		if (rule) {
			state.theory.top()->nodes.emplace_back(unique_ptr<rus::Rule>(rule));
		}
	}
}

template<class T>
void translate_assertion(const Assertion* ass, T* a) {
	a->vars = std::move(translate_vars(ass->outerVars));
	a->disj = std::move(translate_disj(ass));
	uint hc = 0;
	for (const auto& ess : ass->hyps) {
		rus::Expr&& ex = translate_expr(ess.get()->expr, ass);
		a->hyps.emplace_back(new rus::Hyp{hc++, ex});
	}
	rus::Expr&& ex = translate_expr(ass->expr, ass);
	a->props.emplace_back(new rus::Prop{0, ex});
}

void translate_axiom(const Assertion* ass, Maps& state) {
	rus::Axiom* ax = new rus::Axiom(ass->id());
	translate_assertion<rus::Axiom>(ass, ax);
	state.theory.top()->nodes.emplace_back(unique_ptr<rus::Axiom>(ax));
}


inline void count_br(uint s, uint& brack_depth, uint& brace_depth) {
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
	for (auto it = ex.begin() + 1; it != ex.end(); ++ it) {
		count_br(it->lit, brack_depth, brace_depth);
		if (it->lit == eqiv() && low_depth(brack_depth, brace_depth)) return it;
	}
	brack_depth = 0;
	brace_depth = 0;
	for (auto it = ex.begin() + 1; it != ex.end(); ++ it) {
		count_br(it->lit, brack_depth, brace_depth);
		if (it->lit == eqty() && low_depth(brack_depth, brace_depth)) return it;
	}
	return ex.end();
}

void translate_def(const Assertion* ass, Maps& state) {
	rus::Def* def = new rus::Def(ass->id());
	translate_assertion<rus::Def>(ass, def);
	const Expr& ex = ass->expr;
	auto eq_pos = eq_position(ex);

	auto dfm_beg = ex.begin() + 1;
	auto dfm_end = eq_pos;
	auto dfs_beg = eq_pos + 1;
	auto dfs_end = ex.end();

	if (*eq_pos == eqiv()) {
		++ dfm_beg;
		-- dfs_end;
		def->dfm.type.set(wff());
		def->dfs.type.set(wff());
	} else {
		def->dfm.type.set(clas());
		def->dfs.type.set(clas());
	}
	def->prop.type.set(wff());
	for (auto it = ex.begin() + 1; it != ex.end(); ++ it) {
		if ((dfm_beg <= it) && (it < dfm_end)) {
			if (dfm_beg == it)
				def->prop.push_back(rus::Symbol(dfm()));
			def->dfm.push_back(translate_symb(it->lit, ass));
		} else if ((dfs_beg <= it) && (it < dfs_end)) {
			if (dfs_beg == it)
				def->prop.push_back(rus::Symbol(dfs()));
			def->dfs.push_back(translate_symb(it->lit, ass));
		} else {
			def->prop.push_back(translate_symb(it->lit, ass));
		}
	}
	state.theory.top()->nodes.emplace_back(unique_ptr<rus::Def>(def));
}

bool is_def(const Assertion* ass) {
	if (Lex::toStr(ass->id()).substr(0,3) != "df-") return false;
	const Expr& ex = ass->expr;
	auto eq_pos = eq_position(ex);
	return eq_pos != ex.end();
}

rus::Theory::Kind node_kind(const Assertion* ass) {
	if (!is_turnstile(ass->expr.front())) {
		return rus::Theory::RULE;
	} else if (is_def(ass)) {
		return rus::Theory::DEF;
	} else if (!ass->proof.refs.size()) {
		return rus::Theory::AXIOM;
	} else {
		return rus::Theory::THEOREM;
	}
}

rus::Step* translate_step(Tree* tree, rus::Proof* proof, rus::Theorem* thm, Maps& state, const Assertion* a) {
	vector<rus::Proof::Elem>& elems = proof->elems;
	assert(tree->nodes.back().kind() == Tree::Node::REF);
	Tree::Node& node = tree->nodes.back();
	const Assertion* ass = node.ref()->ass();
	rus::Step* step = new rus::Step(elems.size(), rus::Step::ASS, ass->id(), proof);

	for (uint i = 0; i < ass->hyps.size(); ++ i) {
		Tree::Node& n = tree->nodes[i + ass->outerVars.size()];
		assert(n.kind() == Tree::Node::TREE);
		Tree* t = n.tree();
		Tree::Node& h = t->nodes.back();
		assert(h.kind() == Tree::Node::REF);
		rus::Ref* hr =
			h.ref()->is_assertion() ?
			new rus::Ref(translate_step(t, proof, thm, state, a)) :
			new rus::Ref(thm->hyps[h.ref()->index()].get());
		step->refs.emplace_back(hr);
	}
	step->set_ind(elems.size());
	step->expr = translate_expr(node.expr, a);
	elems.emplace_back(unique_ptr<rus::Step>(step));
	return step;
}

void translate_proof(const Assertion* ass, rus::Theorem* thm, Maps& state) {
	Tree* tree = to_tree(&ass->proof);
	tree = reduce(tree, state.redundant_assertions);
	try {
		eval(tree);
	} catch (Error& err) {
		err.msg += "in proof of " + Lex::toStr(ass->id()) + "\n";
		throw err;
	}
	rus::Proof* p = new rus::Proof(thm->id());
	p->allvars = translate_vars(ass->innerVars);
	rus::Step* st = translate_step(tree, p, thm, state, ass);
	rus::Prop* pr = thm->props.front().get();
	p->elems.emplace_back(unique_ptr<rus::Qed>(new rus::Qed(pr, st)));
	state.theory.top()->nodes.emplace_back(unique_ptr<rus::Proof>(p));
	delete tree;
}

void translate_theorem(const Assertion* ass, Maps& state) {
	if (ass->proof.refs.size() == 1 /*&& !ass->proof.refs[0].is_assertion()*/) {
		// Dummy theorem
		return;
	}
	rus::Theorem* thm = new rus::Theorem(ass->id());
	translate_assertion<rus::Theorem>(ass, thm);
	state.theory.top()->nodes.emplace_back(unique_ptr<rus::Theorem>(thm));
	translate_proof(ass, thm, state);
}

void translate_assertion(const Assertion* ass, Maps& state) {
	try {
		switch (node_kind(ass)) {
		case rus::Theory::RULE    : translate_rule(ass, state);    break;
		case rus::Theory::DEF     : translate_def(ass, state);     break;
		case rus::Theory::AXIOM   : translate_axiom(ass, state);   break;
		case rus::Theory::THEOREM : translate_theorem(ass, state); break;
		default : assert(false && "impossible"); break;
		}
	} catch (Error& err) {
		err.msg += "\nat assertion: " + Lex::toStr(ass->id()) + "\n";
		err.msg += "\nsource file: " + Lex::toStr(ass->token.src()->id()) + "\n";
		throw err;
	}
}

void translate_source(uint src, Maps maps, uint tgt = -1);

inline void translate_import(const Import* imp, Maps& s) {
	rus::Import* import = new rus::Import(imp->source.id());
	s.theory.top()->nodes.emplace_back(unique_ptr<rus::Import>(import));
}

inline void translate_comment(const Comment* com, Maps& s) {
	rus::Comment* comment = new rus::Comment { true, com->text };
	s.theory.top()->nodes.emplace_back(unique_ptr<rus::Comment>(comment));
}

void translate_theory(const Source* source, Maps& state) {
	for (auto& node : source->contents) {
		switch (Source::kind(node)) {
		case Source::CONST     : translate_constant(std::get<unique_ptr<Const>>(node).get(), state);      break;
		case Source::IMPORT    : translate_import(std::get<unique_ptr<Import>>(node).get(), state);       break;
		case Source::COMMENT   : translate_comment(std::get<unique_ptr<Comment>>(node).get(), state);     break;
		case Source::ASSERTION : translate_assertion(std::get<unique_ptr<Assertion>>(node).get(), state); break;
		default : assert(false && "impossible"); break;
		}
	}
}

void remove_less_general_rule(rus::Rule* rule, Maps& maps) {
	for (auto& p : maps.rules) {
		rus::Rule* r = p.second;
		if (!r || r == rule) continue;
		bool less_gen = less_general(r, rule);
		bool more_gen = less_general(rule, r);
		if (less_gen && !more_gen) {
			maps.rules.erase(p.first);
			maps.rules[r->id()] = nullptr;
			delete r;
			break;
		} else if (more_gen) {
			maps.rules[rule->id()] = nullptr;
			delete rule;
			break;
		}
	}
}

void translate_super(const Assertion* ass, Maps& state) {
	uint sup = ass->expr[0].lit;
	uint inf = ass->outerVars[0]->type();
	assert(ass->expr[1].lit == ass->outerVars[0]->var());
	if (!state.types.count(sup)) {
		throw Error("super type is not defined", Lex::toStr(sup));
	}
	if (!state.types.count(inf)) {
		throw Error("infer type is not defined", Lex::toStr(inf));
	}
	rus::Type* super = state.types.at(sup);
	rus::Type* infer = state.types.at(inf);

	infer->sup.push_back(super);
	deque<rus::Type*> sup_defs = std::move(state.type_defs[sup]);
	for (auto sup_def = sup_defs.rbegin(); sup_def != sup_defs.rend(); ++ sup_def) {
		state.type_defs[inf].push_front(*sup_def);
	}
}

inline bool rule_term_is_super(const Expr& term) {
	return term.size() == 2 && !term[0].var && term[1].var;
}

Maps create_maps() {
	Maps maps;
	vector<Assertion*> rules;
	vector<Assertion*> supers;
	for (const auto& p : Sys::get().math.get<Assertion>()) {
		Assertion* a = p.second.data;
		if (a->proof.refs.size() == 1) {
			maps.redundant_assertions[a->id()] = &a->proof.refs[0];
		} else {
			if (node_kind(a) == rus::Theory::RULE) {
				for (const auto& v : a->outerVars) {
					translate_type(v.get()->type(), maps);
				}
				translate_type(a->expr.front().lit, maps);
				if (rule_term_is_super(a->expr)) {
					supers.push_back(a);
				} else {
					rules.push_back(a);
				}
			}
		}
	}
	for (Assertion* s : supers) {
		translate_super(s, maps);
	}
	for (Assertion* a : rules) {
		uint id = a->id();
		rus::Rule* rule = new rus::Rule(
			id,
			translate_vars(a->outerVars),
			translate_expr(a->expr, a)
		);
		rule->term.type.set(a->expr[0].lit);
		maps.rules[id] = rule;
		remove_less_general_rule(rule, maps);
	}
	return maps;
}

void translate_source(uint src, Maps maps, uint tgt) {
	tgt = (tgt == -1) ? src : tgt;
	const mm::Source* source = Sys::get().math.get<Source>().access(src);
	rus::Source* target = rus::Sys::mod().math.get<rus::Source>().access(tgt);
	if (target) {
		delete target;
	}
	target = new rus::Source(tgt);
	maps.theory.push(&target->theory);
	translate_theory(Sys::get().math.get<Source>().access(src), maps);
	maps.theory.pop();
}

static vector<uint> find_dependencies(uint src) {
	vector<uint> ret;
	ret.reserve(Sys::get().math.get<Source>().size());
	for (const auto& s : Sys::get().math.get<Source>()) {
		ret.push_back(s.second.data->id());
	}
	return ret;
}

} // anonymous namespace

#define PARALLEL_TRANSLATE

void translate(uint src, uint tgt) {
	if (!Sys::get().math.get<Source>().has(src)) throw Error("no source", Lex::toStr(src));
	Maps maps = create_maps();
	vector<uint> deps = find_dependencies(src);
#ifdef PARALLEL_TRANSLATE
	tbb::parallel_for (tbb::blocked_range<size_t>(0, deps.size()),
		[maps, deps] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				translate_source(deps[i], maps);
			}
		}
	);
#else
	for (uint s : deps) {
		translate_source(s, maps);
	}
#endif
	translate_source(src, maps, tgt);
}

}} // mdl::smm

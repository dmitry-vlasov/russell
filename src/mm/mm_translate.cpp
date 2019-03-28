#include "rus_ast.hpp"
#include "mm_sys.hpp"
#include "mm_math_symb.hpp"
#include "mm_tree.hpp"

namespace mdl {

namespace rus { Rule* create_super(Type* inf, Type* sup); }

namespace mm { namespace {

struct Maps {
	// Global maps
	map<uint, rus::Source*> sources;
	map<uint, deque<rus::Type*>> supers;
	map<uint, rus::Type*> types;
	map<uint, rus::Rule*> rules;
	map<uint, mm::Ref*> redundant_assertions;

	// Local vars
	rus::Source* source = nullptr;
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


inline rus::Token translate_token(const Token& t, const Maps& maps) {
	return rus::Token(maps.sources.at(t.src()->id()), t.beg(), t.end());
}

inline uint translate_const_symb(uint s) {
	auto p = math_consts().find(s);
	if (p == math_consts().end()) {
		return s;
	} else {
		return p->second.symb;
	}
}

inline uint translate_var_symb(uint s) {
	auto p = math_vars().find(s);
	if (p == math_vars().end()) {
		return s;
	} else {
		return p->second.var;
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

inline rus::Symbol* translate_symb(Literal s, const Assertion* ass) {
	if (s.var) {
		uint v = translate_var_symb(s.lit);
		uint t = translate_var_type(s.lit, ass);
		return new rus::Var(v, t, rus::Token());
	} else {
		uint c = translate_const_symb(s.lit);
		return new rus::Const(c, rus::Token());
	}
}

rus::Expr translate_expr(const Expr& ex, const Assertion* ass, const Maps& maps) {
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
				e.symbols.push_back(make_unique<rus::Var>(s, type));
			} else {
				e.symbols.push_back(make_unique<rus::Var>(p->second.var, type));
			}
		} else {
			auto p = math_consts().find(s);
			if (p == math_consts().end()) {
				e.symbols.push_back(make_unique<rus::Const>(s));
			} else {
				e.symbols.push_back(make_unique<rus::Const>(p->second.symb));
			}
		}
	}
	// it's the best what we can do here ...
	e.type.set(wff());
	e.token = translate_token(ass->token, maps);
	return e;
}

void translate_constant(const Const* constant, Maps& state) {
	uint s = constant->symb;
	auto t = state.supers.find(s);
	if (t == state.supers.end()) {
		if (s != turnstile()) {
			rus::Constant* c = nullptr;
			auto p = math_consts().find(s);
			if (p == math_consts().end()) {
				c = new rus::Constant(s, -1, -1);
			} else {
				c = new rus::Constant(p->second.symb, p->second.ascii, p->second.latex);
			}
			c->token.set(state.source);
			state.source->theory.nodes.emplace_back(unique_ptr<rus::Constant>(c));
		}
	} else {
		for (rus::Type* type : t->second) {
			type->token.set(state.source);
			state.source->theory.nodes.emplace_back(unique_ptr<rus::Type>(type));
		}
	}
}

template<typename T>
rus::Vars translate_vars(const vector<T>& decls) {
	vector<rus::Var> vars;
	vars.reserve(decls.size());
	for (const auto& flo : decls) {
		vars.emplace_back(
			translate_var_symb(flo.get()->var()),
			flo.get()->type()
		);
	}
	return rus::Vars(vars);
}

inline rus::Disj translate_disj(const Assertion* ass) {
	return rus::Disj(ass->disj.vect);
}

rus::Type* translate_type(uint t, Maps& state) {
	auto it = state.types.find(t);
	if (it != state.types.end()) {
		return it->second;
	} else {
		rus::Type* type = new rus::Type(t);
		state.types[t] = type;
		state.supers[t].push_back(type);
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
		if (!(*n)->type() && !(*m)->type()) {
			if (*n != *m) {
				return false;
			}
		} else if ((*n)->type() && (*m)->type()) {
			if (!super_type((*n)->type(), (*m)->type())) {
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
			rule->token.set(state.source);
			state.source->theory.nodes.emplace_back(unique_ptr<rus::Rule>(rule));
		}
	}
}

template<class T>
void translate_assertion(const Assertion* ass, T* a, const Maps& maps) {
	a->vars = std::move(translate_vars(ass->outerVars));
	// TODO
	if (a->kind() != rus::Assertion::THM) {
		a->disj = std::move(translate_disj(ass));
	}
	uint hc = 0;
	for (const auto& ess : ass->hyps) {
		rus::Expr&& ex = translate_expr(ess.get()->expr, ass, maps);
		rus::Hyp* hyp = new rus::Hyp{hc++, ex};
		a->hyps.emplace_back(hyp);
		rus::expr::enqueue(hyp->expr);
	}
	rus::Expr&& ex = translate_expr(ass->expr, ass, maps);
	rus::Prop* prop = new rus::Prop{0, ex};
	a->props.emplace_back(prop);
	rus::expr::enqueue(prop->expr);
	a->token.set(maps.source);
}

void translate_axiom(const Assertion* ass, Maps& state) {
	rus::Axiom* ax = new rus::Axiom(ass->id());
	translate_assertion<rus::Axiom>(ass, ax, state);
	state.source->theory.nodes.emplace_back(unique_ptr<rus::Axiom>(ax));
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

vector<Literal>::const_iterator eq_position(const Expr& ex) {
	uint brack_depth = 0;
	uint brace_depth = 0;
	for (auto it = ex.begin() + 1; it != ex.end(); ++ it) {
		count_br(it->literal(), brack_depth, brace_depth);
		if (it->literal() == eqiv() && low_depth(brack_depth, brace_depth)) return it;
	}
	brack_depth = 0;
	brace_depth = 0;
	for (auto it = ex.begin() + 1; it != ex.end(); ++ it) {
		count_br(it->literal(), brack_depth, brace_depth);
		if (it->literal() == eqty() && low_depth(brack_depth, brace_depth)) return it;
	}
	return ex.end();
}

void translate_def(const Assertion* ass, Maps& state) {
	rus::Def* def = new rus::Def(ass->id());
	translate_assertion<rus::Def>(ass, def, state);
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
			if (dfm_beg == it) {
				def->prop.symbols.push_back(make_unique<rus::Literal>(dfm()));
			}
			def->dfm.symbols.emplace_back(translate_symb(*it, ass));
		} else if ((dfs_beg <= it) && (it < dfs_end)) {
			if (dfs_beg == it) {
				def->prop.symbols.push_back(make_unique<rus::Literal>(dfs()));
			}
			def->dfs.symbols.emplace_back(translate_symb(*it, ass));
		} else {
			def->prop.symbols.emplace_back(translate_symb(*it, ass));
		}
	}
	def->dfm.token = translate_token(ass->token, state);
	def->dfs.token = translate_token(ass->token, state);
	rus::expr::enqueue(def->dfm);
	rus::expr::enqueue(def->dfs);
	state.source->theory.nodes.emplace_back(unique_ptr<rus::Def>(def));
}

bool is_def(const Assertion* ass) {
	if (Lex::toStr(ass->id()).substr(0,3) != "df-") return false;
	const Expr& ex = ass->expr;
	auto eq_pos = eq_position(ex);
	return eq_pos != ex.end();
}

rus::Theory::Kind node_kind(const Assertion* ass) {
	if (!ass->expr.front().is_turnstile()) {
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
	step->expr = std::move(translate_expr(node.expr, a, state));
	rus::expr::enqueue(step->expr);
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
	p->allvars = std::move(translate_vars(ass->innerVars));
	rus::Step* st = translate_step(tree, p, thm, state, ass);
	rus::Prop* pr = thm->props.front().get();
	p->elems.emplace_back(unique_ptr<rus::Qed>(new rus::Qed(pr, st)));
	state.source->theory.nodes.emplace_back(unique_ptr<rus::Proof>(p));
	p->token.set(state.source);
	delete tree;
}

void translate_theorem(const Assertion* ass, Maps& state) {
	if (ass->proof.refs.size() == 1) {
		// Dummy theorem
		return;
	}
	rus::Theorem* thm = new rus::Theorem(ass->id());
	translate_assertion<rus::Theorem>(ass, thm, state);
	state.source->theory.nodes.emplace_back(unique_ptr<rus::Theorem>(thm));
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

inline void translate_import(const Import* imp, Maps& maps) {
	rus::Import* import = new rus::Import(
		imp->source.id(),
		rus::Token(maps.sources.at(imp->token.src()->id()), imp->token.beg(), imp->token.end())
	);
	maps.source->theory.nodes.emplace_back(unique_ptr<rus::Import>(import));
}

inline void translate_comment(const Comment* com, Maps& s) {
	rus::Comment* comment = new rus::Comment { true, com->text };
	s.source->theory.nodes.emplace_back(unique_ptr<rus::Comment>(comment));
}

void translate_theory(uint src, Maps state) {
	const mm::Source* source = Sys::get().math.get<Source>().access(src);
	state.source = state.sources.at(src);
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

	infer->sup.push_back(rus::User<rus::Type>(super));
	deque<rus::Type*> sup_defs = std::move(state.supers[sup]);
	for (auto sup_def = sup_defs.rbegin(); sup_def != sup_defs.rend(); ++ sup_def) {
		state.supers[inf].push_front(*sup_def);
	}
	rus::Rule* rule = rus::create_super(infer, super);
	rule->token.set(state.sources.at(ass->token.src()->id()));
	state.rules[rule->id()] = rule;
}

inline bool rule_term_is_super(const Expr& term) {
	return term.size() == 2 && !term[0].var && term[1].var;
}

rus::Source* create_source(uint src, Maps& maps, uint tgt = -1) {
	if (maps.sources.find(src) != maps.sources.end()) {
		return maps.sources.at(src);
	}
	tgt = (tgt == -1) ? src : tgt;
	const mm::Source* source = Sys::get().math.get<Source>().access(src);
	if (rus::Source* target = rus::Sys::mod().math.get<rus::Source>().access(tgt)) {
		delete target;
	}
	rus::Source* target = new rus::Source(tgt);
	maps.sources[src] = target;
	for (auto& n : source->contents) {
		if (mm::Source::kind(n) == mm::Source::IMPORT) {
			mm::Import* imp = std::get<unique_ptr<Import>>(n).get();
			rus::Source* inc = create_source(imp->source.id(), maps);
			target->include(inc);
		}
	}
	return target;
}

Maps create_maps(uint src, uint tgt) {
	Maps maps;
	vector<rus::Source*> targets;
	Sys::mod().math.get<Source>().rehash();
	for (const auto& p : Sys::get().math.get<Source>()) {
		if (p.first == src) {
			targets.push_back(create_source(src, maps, tgt));
		} else {
			targets.push_back(create_source(p.first, maps));
		}
	}
	for (auto t : targets) {
		t->transitive_closure();
	}
	vector<Assertion*> rules;
	vector<Assertion*> supers;
	Sys::mod().math.get<Assertion>().rehash();
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
		rus::Rule* rule = new rus::Rule(id);
		rule->vars = std::move(translate_vars(a->outerVars));
		rule->term = std::move(translate_expr(a->expr, a, maps));
		rule->term.type.set(a->expr[0].lit);
		rule->token = translate_token(a->token, maps);
		create_rule_term(rule->term, id);
		maps.rules[id] = rule;
		remove_less_general_rule(rule, maps);
	}
	return maps;
}

static vector<uint> find_dependencies(uint src) {
	vector<uint> ret;
	ret.reserve(Sys::get().math.get<Source>().size());
	for (const auto& s : Sys::get().math.get<Source>()) {
		ret.push_back(s.second.data->id());
	}
	ret.push_back(src);
	return ret;
}

} // anonymous namespace

#ifdef PARALLEL
#define PARALLEL_MM_TRANSLATE
#endif

void translate(uint src, uint tgt) {
	if (!Sys::get().math.get<Source>().has(src)) {
		throw Error("no source", Lex::toStr(src));
	}
	Maps maps = create_maps(src, tgt);
	vector<uint> deps = find_dependencies(src);
#ifdef PARALLEL_MM_TRANSLATE
	tbb::parallel_for (tbb::blocked_range<size_t>(0, deps.size()),
		[maps, deps] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				translate_theory(deps[i], maps);
			}
		}
	);
#else
	for (uint s : deps) {
		translate_theory(s, maps);
	}
#endif
}

}} // mdl::smm

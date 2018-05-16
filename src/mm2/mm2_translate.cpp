#include <rus_ast.hpp>
#include <mm2_sys.hpp>
#include "mm2_math_symb.hpp"
#include "mm2_tree.hpp"

namespace mdl { namespace mm2 { namespace {

typedef vector<rus::Node>::iterator NodeIter;

struct Maps {
	map<const rus::Rule*,  rus::Theory*> rule_theory;
	map<const rus::Type*,  rus::Theory*> type_theory;
	map<const mm2::Source*,rus::Source*> sources;
	map<mm2::Symbol, rus::Type*>         types;
	set<rus::Rule*>                      rules;
	map<const rus::Type*, uint>          inds;

	rus::Type*  type_wff;
	rus::Type*  type_set;
	rus::Type*  type_class;
	set<mm2::Symbol>     redundant_consts;
	map<uint, mm2::Ref*> redundant_assertions;
	stack<rus::Theory*>  theory;
};

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

rus::Expr translate_expr(const Expr& ex, const Maps& state, const Assertion* ass) {
	rus::Expr e;
	for (auto it = ex.begin(); it != ex.end(); ++ it) {
		// pass the first symbol
		if (it == ex.begin()) continue;
		e.push_back(translate_symb(*it, ass));
	}
	// it's the best what we can do here ...
	e.type = state.type_wff;
	return e;
}

void translate_constant(const Const* constant, Maps& state) {
	uint s = constant->symb;
	if (state.redundant_consts.count(s)) return;
	rus::Const* c = nullptr;
	auto p = math_consts().find(s);
	if (p == math_consts().end()) {
		c = new rus::Const(s, rus::Symbol::undef(), rus::Symbol::undef());
	} else {
		c = new rus::Const(p->second.symb, p->second.ascii, p->second.latex);
	}
	state.theory.top()->nodes.emplace_back(c);
}

rus::Type* translate_type(Symbol type_sy, Maps& state);

template<typename T>
rus::Vars translate_vars(const vector<T>& decls) {
	rus::Vars rus_vars;
	for (const auto& flo : decls) {
		rus_vars.v.push_back(translate_var(flo.get()->var(), flo.get()->type()));
	}
	return rus_vars;
}

rus::Disj translate_disj(const Assertion* ass, Maps& state) {
	rus::Disj rus_disj;
	for (const auto& dis : ass->disj.vect) {
		rus_disj.d.push_back(vector<rus::Symbol>());
		vector<rus::Symbol>& rus_dis = rus_disj.d.back();
		for (auto v : *dis.get()) {
			rus::Type* type = nullptr;
			for (const auto& flo : ass->outerVars) {
				if (flo.get()->var() == v) {
					type = translate_type(flo.get()->type(), state);
				}
			}
			for (const auto& inn : ass->innerVars) {
				if (inn.get()->var() == v) {
					type = translate_type(inn.get()->type(), state);
				}
			}
			if (!type) {
				throw Error("untyped var", show_sy(v));
			}
			rus::Symbol rv = translate_var(v, type->id());
			rus_dis.push_back(rv);
		}
	}
	return rus_disj;
}

rus::Type* translate_type(Symbol type_sy, Maps& state) {
	if (state.types.count(type_sy))
		return state.types.find(type_sy)->second;
	else {
		string type_str = Lex::toStr(type_sy.lit);
		uint type_id = Lex::toInt(type_str);
		rus::Type* type = new rus::Type(type_id);
		static uint ind = 0;
		state.inds[type] = ind ++;
		state.types[type_sy] = type;
		state.theory.top()->nodes.push_back(type);
		state.type_theory[type] = state.theory.top();
		if (type_str == "wff") state.type_wff = type;
		if (type_str == "set") state.type_set = type;
		if (type_str == "class") state.type_class = type;
		return type;
	}
}

void translate_super(const Assertion* ass, Maps& state) {
	Symbol super_sy = ass->expr[0];
	Symbol infer_sy = ass->outerVars[0]->type();
	assert(ass->expr[1] == ass->outerVars[0]->var());
	rus::Type* super = translate_type(super_sy, state);
	rus::Type* infer = translate_type(infer_sy, state);
	infer->sup.push_back(super);
	if (state.inds[infer] < state.inds[super]) {
		rus::Theory* sup_th = state.type_theory[super];
		rus::Theory* inf_th = state.type_theory[infer];
		NodeIter sup = find(sup_th->nodes.begin(), sup_th->nodes.end(), rus::Node(super));
		NodeIter inf = find(inf_th->nodes.begin(), inf_th->nodes.end(), rus::Node(infer));
		sup_th->nodes.erase(sup);
		inf_th->nodes.insert(inf, super);
	}
}

inline bool super_type(const rus::Type* t1, const rus::Type* t2) {
	if (t1 == t2) return true;
	for (auto& s : t1->sup)
		if (t2 == s)
			return true;
	return false;

}

bool less_general(const rus::Rule* r1, const rus::Rule* r2) {
	if (!super_type(r2->term.type.get(), r1->term.type.get()))
		return false;
	auto n = r1->term.symbols.begin();
	auto n_end = r1->term.symbols.end();
	auto m = r2->term.symbols.begin();
	auto m_end = r2->term.symbols.end();
	while (n != n_end && m != m_end) {
		if (!n->type() && !m->type()) {
			if (*n != *m)
				return false;
		} else if (n->type() && m->type()) {
			if (!super_type(n->type(), m->type()))
				return false;
		} else {
			return false;
		}
		++ n; ++ m;
	}
	return n == n_end && m == m_end;
}

inline bool rule_term_is_super(const Expr& term) {
	return term.size() == 2 && !term[0].var && term[1].var;
}

void translate_rule(const Assertion* ass, Maps& state) {
	if (rule_term_is_super(ass->expr)) {
		translate_super(ass, state);
		return;
	}
	rus::Type* type = translate_type(ass->expr[0], state);

	rus::Rule* rule = new rus::Rule(
		ass->id(),
		translate_vars(ass->outerVars),
		translate_expr(ass->expr, state, ass)
	);
	rule->term.type = rus::User<rus::Type>(type->id());

	for (rus::Rule* r : state.rules) {
		bool less_gen = less_general(r, rule);
		bool more_gen = less_general(rule, r);
		if (less_gen && !more_gen) {
			rus::Theory* th = state.rule_theory[r];
			NodeIter it = find(th->nodes.begin(), th->nodes.end(), rus::Node(r));
			state.rules.erase(r);
			delete it->val.rul;
			it->val.rul = rule;
			return;
		} else if (more_gen) {
			delete rule;
			return;
		}
	}
	state.theory.top()->nodes.push_back(rule);
	state.rule_theory[rule] = state.theory.top();
	state.rules.insert(rule);
}

template<class T>
void translate_assertion(const Assertion* ass, T* a, Maps& state) {
	a->vars = translate_vars(ass->outerVars);
	a->disj = translate_disj(ass, state);
	uint hc = 0;
	for (const auto& ess : ass->hyps) {
		rus::Expr&& ex = translate_expr(ess.get()->expr, state, ass);
		a->hyps.push_back(new rus::Hyp{hc++, ex});
	}
	rus::Expr&& ex = translate_expr(ass->expr, state, ass);
	a->props.push_back(new rus::Prop{0, ex});
}

void translate_axiom(const Assertion* ass, Maps& state) {
	rus::Axiom* ax = new rus::Axiom(ass->id());
	translate_assertion<rus::Axiom>(ass, ax, state);
	state.theory.top()->nodes.push_back(ax);
}

inline Symbol open_brace() { return Symbol(Lex::toInt("{")); }
inline Symbol close_brace() {return Symbol(Lex::toInt("}")); }
inline Symbol open_brack() { return Symbol(Lex::toInt("(")); }
inline Symbol close_brack() { return Symbol(Lex::toInt(")")); }
inline Symbol eqty() { return Symbol(Lex::toInt("=")); }
inline Symbol eqiv() { return Symbol(Lex::toInt("<->")); }
inline Symbol dfm() { return Symbol(Lex::toInt("defiendum")); }
inline Symbol dfs() { return Symbol(Lex::toInt("definiens")); }

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
	for (auto it = ex.begin() + 1; it != ex.end(); ++ it) {
		count_br(*it, brack_depth, brace_depth);
		if (*it == eqiv() && low_depth(brack_depth, brace_depth)) return it;
	}
	brack_depth = 0;
	brace_depth = 0;
	for (auto it = ex.begin() + 1; it != ex.end(); ++ it) {
		count_br(*it, brack_depth, brace_depth);
		if (*it == eqty() && low_depth(brack_depth, brace_depth)) return it;
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
		def->dfm.type = state.type_wff;
		def->dfs.type = state.type_wff;
	} else {
		def->dfm.type = state.type_class;
		def->dfs.type = state.type_class;
	}
	def->prop.type = state.type_wff;
	for (auto it = ex.begin() + 1; it != ex.end(); ++ it) {
		if ((dfm_beg <= it) && (it < dfm_end)) {
			if (dfm_beg == it)
				def->prop.push_back(rus::Symbol(dfm().lit));
			def->dfm.push_back(translate_symb(it->lit, ass));
		} else if ((dfs_beg <= it) && (it < dfs_end)) {
			if (dfs_beg == it)
				def->prop.push_back(rus::Symbol(dfs().lit));
			def->dfs.push_back(translate_symb(it->lit, ass));
		} else {
			def->prop.push_back(translate_symb(it->lit, ass));
		}
	}
	state.theory.top()->nodes.push_back(def);
}

bool is_def(const Assertion* ass) {
	if (Lex::toStr(ass->id()).substr(0,3) != "df-") return false;
	const Expr& ex = ass->expr;
	auto eq_pos = eq_position(ex);
	return eq_pos != ex.end();
}

rus::Node::Kind node_kind(const Assertion* ass) {
	if (!is_turnstile(ass->expr.front())) {
		return rus::Node::RULE;
	} else if (is_def(ass)) {
		return rus::Node::DEF;
	} else if (!ass->proof.refs.size()) {
		return rus::Node::AXIOM;
	} else {
		return rus::Node::THEOREM;
	}
}

rus::Proof::Elem translate_step(Tree* tree, rus::Proof* proof, rus::Theorem* thm, Maps& state, const Assertion* a) {
	vector<rus::Proof::Elem>& elems = proof->elems;
	assert(tree->nodes.back().type == Tree::Node::REF);
	Tree::Node& node = tree->nodes.back();
	const Assertion* ass = node.val.ref->ass();
	rus::Proof::Elem el(new rus::Step(elems.size(), rus::Step::ASS, ass->id(), proof));

	for (uint i = 0; i < ass->hyps.size(); ++ i) {
		Tree::Node& n = tree->nodes[i + ass->outerVars.size()];
		assert(n.type == Tree::Node::TREE);
		Tree* t = n.val.tree;
		Tree::Node& h = t->nodes.back();
		assert(h.type == Tree::Node::REF);
		rus::Ref* hr =
			h.val.ref->is_assertion() ?
			new rus::Ref(translate_step(t, proof, thm, state, a).val.step) :
			new rus::Ref(thm->hyps[h.val.ref->index()]);
		el.val.step->refs.push_back(hr);
	}
	el.val.step->set_ind(elems.size());
	el.val.step->expr = translate_expr(node.expr, state, a);
	elems.push_back(el);
	return el;
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
	p->vars = translate_vars(ass->innerVars);
	translate_step(tree, p, thm, state, ass);
	rus::Prop* pr = thm->props.front();
	rus::Step* st = p->elems.back().val.step;
	p->elems.push_back(new rus::Qed(pr, st));
	state.theory.top()->nodes.push_back(p);
	delete tree;
}

void translate_theorem(const Assertion* ass, Maps& state) {
	if (ass->proof.refs.size() == 1 /*&& !ass->proof.refs[0].is_assertion()*/) {
		// Dummy theorem
		return;
	}
	rus::Theorem* thm = new rus::Theorem(ass->id());
	translate_assertion<rus::Theorem>(ass, thm, state);
	state.theory.top()->nodes.push_back(thm);
	translate_proof(ass, thm, state);
}

void translate_assertion(const Assertion* ass, Maps& state) {
	try {
		switch (node_kind(ass)) {
		case rus::Node::RULE    : translate_rule(ass, state);    break;
		case rus::Node::DEF     : translate_def(ass, state);     break;
		case rus::Node::AXIOM   : translate_axiom(ass, state);   break;
		case rus::Node::THEOREM : translate_theorem(ass, state); break;
		default : assert(false && "impossible"); break;
		}
	} catch (Error& err) {
		err.msg += "\nat assertion: " + Lex::toStr(ass->id()) + "\n";
		err.msg += "\nsource file: " + Lex::toStr(ass->token.src()->id()) + "\n";
		throw err;
	}
}

rus::Source* translate_source(const Source* source, Maps& state, rus::Source* target = nullptr);

inline rus::Import* translate_import(const Import* inc, Maps& s) {
	const rus::Source* src = translate_source(inc->source.get(), s);
	return new rus::Import(src->id(), false);
}

inline void translate_comment(const Comment* com, Maps& s) {
	rus::Comment* comment = new rus::Comment { com->text };
	s.theory.top()->nodes.push_back(comment);
}

void translate_theory(const Source* source, Maps& state) {
	for (const auto& node : source->contents) {
		if (auto imp = std::get_if<unique_ptr<Import>>(&node)) {
			state.theory.top()->nodes.push_back(translate_import(imp->get(), state));
		}
	}
	for (auto& node : source->contents) {
		switch (node.index()) {
		case 0 : translate_constant(std::get<unique_ptr<Const>>(node).get(), state);  break;
		case 1 : break;
		case 2 : translate_comment(std::get<unique_ptr<Comment>>(node).get(), state);   break;
		case 3 : translate_assertion(std::get<unique_ptr<Assertion>>(node).get(), state); break;
		default : assert(false && "impossible"); break;
		}
	}
}

rus::Source* translate_source(const Source* src, Maps& state, rus::Source* target) {
	if (state.sources.count(src)) {
		return state.sources[src];
	} else {
		if (!target) {
			delete rus::Sys::get().math.get<rus::Source>().access(src->id());
			target = new rus::Source(src->id());
			target->theory = new rus::Theory();
		}
		state.sources[src] = target;
		state.theory.push(target->theory);
		translate_theory(src, state);
		state.theory.pop();
		return target;
	}
}

} // anonymous namespace

void translate(uint src, uint tgt) {
	const Source* source = Sys::get().math.get<Source>().access(src);
	if (!source) throw Error("no source", Lex::toStr(src));
	delete rus::Sys::get().math.get<rus::Source>().access(tgt);
	rus::Source* target = new rus::Source(tgt);
	target->theory = new rus::Theory();
	Maps state;
	for (auto& p : Sys::get().math.get<Assertion>()) {
		Assertion* a = p.second.data;
		if (a->proof.refs.size() == 1) {
			state.redundant_assertions[a->id()] = &a->proof.refs[0];
		}
	}
	state.type_wff = nullptr;
	state.type_set = nullptr;
	state.type_class = nullptr;
	state.redundant_consts.insert(Lex::getInt("wff"));
	state.redundant_consts.insert(Lex::getInt("set"));
	state.redundant_consts.insert(Lex::getInt("class"));
	state.redundant_consts.insert(Lex::getInt("|-"));
	translate_source(source, state, target);
}

}} // mdl::smm

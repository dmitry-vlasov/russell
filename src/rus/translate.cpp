#include "smm/ast.hpp"
#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace {

struct Maps {
	Map<const Assertion*, Map<const Hyp*, smm::Essential*>> essentials;
	Map<const Assertion*, Map<Symbol, smm::Floating*>> floatings;
	Map<const Assertion*, Map<Symbol, smm::Inner*>> inners;
	Map<const Assertion*, smm::Assertion*> assertions;
	Map<const Type*, uint> types;
	Map<const Rule*, smm::Assertion*> rules;
	Map<const Rule*, Map<Symbol, uint>> rules_args;
	Map<const Source*, smm::Source*> sources;
	smm::Assertion* thm;
	mdl::Symbol turnstile;
};

inline uint translate_symb(uint s) {
	if (!Rus::get().math.consts.has(s))
		return s;
	else {
		Const* c = Rus::get().math.consts[s];
		return c->ascii.lit == static_cast<uint>(-1) ? s : c->ascii.lit;
	}
}

mdl::Expr translate_expr(const Expr& ex, Maps& maps) {
	mdl::Expr expr;
	expr += maps.turnstile;
	for (auto it = ex.term.begin(); it != ex.term.end(); ++ it)
		expr += mdl::Symbol(translate_symb(it->symb.lit), it->symb.type);
	return expr;
}

mdl::Expr translate_term(const Expr& ex, const Type* tp, Maps& maps) {
	mdl::Expr expr;
	expr += mdl::Symbol(maps.types[tp]);
	for (auto it = ex.term.begin(); it != ex.term.end(); ++ it)
		expr += mdl::Symbol(translate_symb(it->symb.lit), it->symb.type);
	return expr;
}

smm::Constants* translate_const(const Const* c, Maps& maps) {
	smm::Constants* consts = new smm::Constants;
	static bool first_time = true;
	if (first_time) {
		uint ts = Rus::mod().lex.symbs.toInt("|-");
		maps.turnstile = mdl::Symbol(ts);
		consts->expr += maps.turnstile;
		first_time = false;
	}
	consts->expr += mdl::Symbol(translate_symb(c->symb.lit));
	return consts;
}

smm::Variables* translate_vars(const Vars& rvars) {
	smm::Variables* svars = new smm::Variables;
	for (auto s : rvars.v)
		svars->expr += mdl::Symbol(s.lit, true);
	return svars;
}

vector<smm::Disjointed*> translate_disj(const Disj& rdisj) {
	vector<smm::Disjointed*> disj_vect;
	for (auto d : rdisj.d) {
		smm::Disjointed* disj = new smm::Disjointed;
		for (auto s : d)
			disj->expr += mdl::Symbol(s.lit, true);
		disj_vect.push_back(disj);
	}
	return disj_vect;
}

smm::Assertion* translate_rule(const Rule* rule, Maps& maps);

vector<smm::Node> translate_type(const Type* type, Maps& maps) {
	string type_str = Rus::get().lex.ids.toStr(type->id);
	uint type_sy = Rus::mod().lex.symbs.toInt(type_str);
	maps.types[type] = type_sy;
	smm::Constants* consts = new smm::Constants;
	consts->expr += type_sy;
	vector<smm::Node> ret;
	ret.push_back(consts);
	for (auto p : type->supers)
		ret.push_back(translate_rule(p.second, maps));
	return ret;
}

vector<smm::Essential*> translate_essentials(const Assertion* ass, Maps& maps) {
	vector<smm::Essential*> ess_vect;
	for (auto hyp : ass->hyps) {
		smm::Essential* ess = new smm::Essential;
		ess->index = hyp->ind;
		ess->expr = translate_expr(hyp->expr, maps);
		ess_vect.push_back(ess);
		maps.essentials[ass][hyp] = ess;
	}
	return ess_vect;
}

vector<smm::Floating*> translate_floatings(const Vars& vars, Maps& maps, const Assertion* ass = nullptr) {
	vector<smm::Floating*> flo_vect;
	for (uint i = 0; i < vars.v.size(); ++ i) {
		Symbol v = vars.v[i];
		smm::Floating* flo = new smm::Floating;
		flo->index = i;
		flo->expr += mdl::Symbol(maps.types[v.type]);
		flo->expr += mdl::Symbol(v.lit, true);
		flo_vect.push_back(flo);
		if (ass) maps.floatings[ass][v] = flo;
	}
	return flo_vect;
}

smm::Assertion* translate_rule(const Rule* rule, Maps& maps) {
	smm::Assertion* ra = new smm::Assertion();
	if (rule->vars.v.size())
		ra->variables.push_back(translate_vars(rule->vars));
	ra->floating = translate_floatings(rule->vars, maps);
	ra->prop.axiom = true;
	ra->prop.expr  = translate_term(rule->term, rule->type, maps);
	string rule_str = Rus::get().lex.ids.toStr(rule->id);
	uint rule_lab = Rus::mod().lex.ids.toInt(rule_str);
	ra->prop.label = rule_lab;
	maps.rules[rule] = ra;
	for (auto v : rule->vars.v) {
		uint i = 0;
		for (auto& ch : rule->term.term.children) {
			if (ch.getvar() == v) {
				maps.rules_args[rule][v] = i;
				break;
			}
			++ i;
		}
	}
	return ra;
}

vector<smm::Node> translate_assertion(const Assertion* ass, Maps& maps) {
	vector<smm::Node> ra_vect;
	for (auto prop : ass->props) {
		smm::Assertion* ra = new smm::Assertion();
		if (ass->vars.v.size())
			ra->variables.push_back(translate_vars(ass->vars));
		if (ass->disj.d.size())
			ra->disjointed = translate_disj(ass->disj);
		ra->floating = translate_floatings(ass->vars, maps, ass);
		ra->essential= translate_essentials(ass, maps);
		ra->prop.expr  = translate_expr(prop->expr, maps);
		string ass_str = Rus::get().lex.ids.toStr(ass->id);
		if (prop->ind)
			ass_str += "_" + to_string(prop->ind);
		uint ass_lab = Rus::mod().lex.ids.toInt(ass_str);
		ra->prop.label = ass_lab;
		ra_vect.push_back(ra);
		maps.assertions[ass] = ra;
	}
	return ra_vect;
}

vector<smm::Node> translate_axiom(const Axiom* ax, Maps& maps) {
	vector<smm::Node> asss = translate_assertion(&ax->ass, maps);
	for (auto n : asss) {
		assert(n.type == smm::Node::ASSERTION);
		n.val.ass->prop.axiom = true;
	}
	return asss;
}

vector<smm::Node> translate_def(const Def* ax, Maps& maps) {
	vector<smm::Node> asss = translate_assertion(&ax->ass, maps);
	for (auto n : asss) {
		assert(n.type == smm::Node::ASSERTION);
		n.val.ass->prop.axiom = true;
	}
	return asss;
}


void translate_step(const Step* st, const Assertion* thm, vector<smm::Ref>& smm_proof, Maps& maps);

void translate_ref(Ref ref, const Assertion* thm, vector<smm::Ref>& smm_proof, Maps& maps) {
	switch (ref.kind) {
	case Ref::HYP:  smm_proof.push_back(smm::Ref(maps.essentials[thm][ref.val.hyp])); break;
	case Ref::PROP: break;
	case Ref::STEP: translate_step(ref.val.step, thm, smm_proof, maps); break;
	default : assert(false); break;
	}
}

void translate_term(const term::Expr& t, const Assertion* thm, vector<smm::Ref>& smm_proof, Maps& maps) {
	if (t.isvar()) {
		if (maps.floatings[thm].has(t.getvar()))
			smm_proof.push_back(maps.floatings[thm][t.getvar()]);
		else if (maps.inners[thm].has(t.getvar()))
			smm_proof.push_back(maps.inners[thm][t.getvar()]);
		else
			throw Error("undeclared variable", show(t.getvar()));
	} else {
		for (auto v : t.rule->vars.v)
			translate_term(t.children[maps.rules_args[t.rule][v]], thm, smm_proof, maps);
	}
	if (t.rule) {
		if (!maps.rules.has(t.rule))
			throw Error("undefined reference to rule");
		smm_proof.push_back(smm::Ref(maps.rules[t.rule], true));
	}
}

void translate_proof(const Proof* proof, const Assertion* thm, vector<smm::Ref>& smm_proof, Maps& maps, uint ind = 0);

void translate_step(const Step* st, const Assertion* thm, vector<smm::Ref>& smm_proof, Maps& maps) {
	if (st->kind == Step::CLAIM) {
		translate_proof(st->val.prf, thm, smm_proof, maps);
		return;
	}
	for (auto ref : st->refs)
		translate_ref(ref, thm, smm_proof, maps);
	const Assertion* ass = st->assertion();
	sub::Expr* ps = unify(ass->props[0]->expr, st->expr);
	if (!ps) throw Error("proposition unification failed");
	for (uint i = 0; i < ass->arity(); ++ i) {
		sub::Expr* hs = unify(ass->hyps[i]->expr, st->refs[i].expr());
		if (!hs) throw Error("hypothesis unification failed");
		if (!ps->join(hs)) throw Error("substitution join failed");
		delete hs;
	}
	for (auto v : st->assertion()->vars.v)
		translate_term(ps->find(v), thm, smm_proof, maps);
	delete ps;
	if (!maps.assertions.has(ass))
		throw Error("undefined reference to assertion");
	assert(maps.assertions.has(ass));
	smm_proof.push_back(smm::Ref(maps.assertions[ass], st->kind != Step::THM));
}

vector<smm::Inner*> translate_inners(const Vars& vars, Maps& maps, const Assertion* thm, uint ind_0) {
	vector<smm::Inner*> inn_vect;
	smm::Variables* smm_vars = nullptr;
	if (vars.v.size()) {
		maps.thm->variables.push_back(new smm::Variables);
		smm_vars = maps.thm->variables.back();
	}
	for (uint i = 0; i < vars.v.size(); ++ i) {
		Symbol v = vars.v[i];
		smm::Inner* inn = new smm::Inner;
		inn->index = i + ind_0;
		inn->expr += mdl::Symbol(maps.types[v.type]);
		inn->expr += mdl::Symbol(v.lit, true);
		inn_vect.push_back(inn);
		smm_vars->expr.push_back(mdl::Symbol(v.lit, true));
		maps.inners[thm][v] = inn;
	}
	return inn_vect;
}

void translate_proof(const Proof* proof, const Assertion* thm, vector<smm::Ref>& smm_proof, Maps& maps, uint ind) {
	join(maps.thm->inner, translate_inners(proof->vars, maps, thm, maps.thm->inner.size()));
	for (auto el : proof->elems) {
		if (el.kind == Proof::Elem::QED && el.val.qed->prop->ind == ind) {
			translate_step(el.val.qed->step, thm, smm_proof, maps);
			break;
		}
	}
}

vector<smm::Node> translate_proof(const Proof* proof, Maps& maps) {
	vector<smm::Node> nodes;
	vector<smm::Node> asss = translate_assertion(&proof->thm->ass, maps);
	if (proof->id != static_cast<uint>(-1)) {
		// TODO
	}
	for (uint i = 0; i < asss.size(); ++ i) {
		maps.thm = asss[i].val.ass;
		maps.thm->proof = new smm::Proof();
		translate_proof(proof, &proof->thm->ass, maps.thm->proof->refs, maps, i);
	}
	join(nodes, asss);
	return nodes;
}

smm::Source* translate_source(const Source* src, Maps& maps, smm::Source* target = nullptr);

inline smm::Inclusion* translate_import(const Import* imp, Maps& maps) {
	smm::Source* src = translate_source(imp->source, maps);
	return new smm::Inclusion(src, imp->primary);
}

vector<smm::Node> translate_theory(const Theory* thy, Maps& maps) {
	vector<smm::Node> nodes;
	for (auto n : thy->nodes) {
		switch (n.kind) {
		case Node::CONST:   nodes.push_back(translate_const(n.val.cst, maps));  break;
		case Node::TYPE:    join(nodes, translate_type(n.val.tp, maps));        break;
		case Node::RULE:    nodes.push_back(translate_rule(n.val.rul, maps));   break;
		case Node::AXIOM:   join(nodes, translate_axiom(n.val.ax, maps));       break;
		case Node::DEF:     join(nodes, translate_def(n.val.def, maps));        break;
		case Node::THEOREM: break;  // theorem is translated implicitly in proof
		case Node::PROOF:   join(nodes, translate_proof(n.val.prf, maps));      break;
		case Node::THEORY:  join(nodes, translate_theory(n.val.thy, maps));     break;
		case Node::IMPORT:  nodes.push_back(translate_import(n.val.imp, maps)); break;
		case Node::COMMENT: nodes.push_back(new smm::Comment(n.val.com->text)); break;
		default : assert(false && "impossible"); break;
		}
	}
	return nodes;
}

smm::Source* translate_source(const Source* src, Maps& maps, smm::Source* target) {
	if (maps.sources.has(src)) {
		return maps.sources[src];
	} else {
		Config conf = Rus::get().config;
		if (!target)
			target = new smm::Source(
				conf.deep ? conf.out : conf.root,
				src->name
			);
		maps.sources[src] = target;
		target->contents = translate_theory(src->theory, maps);
		return target;
	}
}

}

smm::Source* translate(const Source* src) {
	Config conf = Rus::get().config;
	smm::Source* target = new smm::Source(
		conf.deep ? conf.out : conf.root,
		conf.deep ? conf.in  : conf.out
	);
	Maps maps;
	maps.thm = nullptr;
	return translate_source(src, maps, target);
}

}} // mdl::rus

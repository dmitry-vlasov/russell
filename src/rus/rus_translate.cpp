#include <rus_ast.hpp>
#include <smm_ast.hpp>

namespace mdl { namespace rus { namespace {

struct Maps {
	Maps() : thm(nullptr), first_time(true) { }
	map<const Assertion*, map<const Hyp*, smm::Essential*>> essentials;
	map<const Assertion*, map<Symbol, smm::Floating*>> floatings;
	map<const Assertion*, map<Symbol, smm::Inner*>> inners;
	map<const Assertion*, smm::Assertion*> assertions;
	map<const Type*, uint> types;
	map<const Rule*, smm::Assertion*> rules;
	map<const Rule*, map<Symbol, uint>> rules_args;
	map<const Source*, smm::Source*> sources;
	smm::Assertion* thm;
	mdl::Symbol turnstile;
	bool first_time;
};

inline uint translate_symb(const Symbol& s) {
	if (s.cst) {
		const Const* c = s.constant();
		return mdl::Symbol::is_undef(c->ascii) ? s.lit : c->ascii;
	} else
		return s.lit;
}

mdl::Vect translate_expr(const Expr& ex, Maps& maps) {
	mdl::Vect expr;
	expr += maps.turnstile;
	for (auto& s : ex.symbols) expr += mdl::Symbol(translate_symb(s), s.type());
	return expr;
}

mdl::Vect translate_term(const Expr& ex, const Type* tp, Maps& maps) {
	mdl::Vect expr;
	expr += mdl::Symbol(maps.types[tp]);
	for (auto& s : ex.symbols) expr += mdl::Symbol(translate_symb(s), s.type());
	return expr;
}

smm::Constant* translate_turnstile(Maps& maps) {
	uint ts = Lex::toInt("|-");
	maps.turnstile = mdl::Symbol(ts);
	smm::Constant* constant = new smm::Constant(maps.turnstile);
	return constant;
}

smm::Constant* translate_const(const Const* c, Maps& maps) {
	uint symb = mdl::Symbol::is_undef(c->ascii) ? c->id() : c->ascii;
	smm::Constant* constant = new smm::Constant(symb);
	return constant;
}

smm::Variables* translate_vars(const Vars& rvars) {
	smm::Variables* svars = new smm::Variables();
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
	string type_str = Lex::toStr(type->id());
	uint type_sy = Lex::toInt(type_str);
	maps.types[type] = type_sy;
	smm::Constant* constant = new smm::Constant(type_sy);
	vector<smm::Node> ret;
	ret.push_back(constant);
	for (auto p : type->supers)
		ret.push_back(translate_rule(p.second, maps));
	return ret;
}

vector<smm::Essential*> translate_essentials(const Assertion* ass, Maps& maps) {
	vector<smm::Essential*> ess_vect;
	for (auto hyp : ass->hyps) {
		smm::Essential* ess = new smm::Essential(hyp->ind, translate_expr(hyp->expr, maps));
		ess_vect.push_back(ess);
		maps.essentials[ass][hyp] = ess;
	}
	return ess_vect;
}

vector<smm::Floating*> translate_floatings(const Vars& vars, Maps& maps, const Assertion* ass = nullptr) {
	vector<smm::Floating*> flo_vect;
	for (uint i = 0; i < vars.v.size(); ++ i) {
		Symbol v = vars.v[i];
		smm::Floating* flo = new smm::Floating(i);
		flo->expr += mdl::Symbol(maps.types[v.type()]);
		flo->expr += mdl::Symbol(v.lit, true);
		flo_vect.push_back(flo);
		if (ass) maps.floatings[ass][v] = flo;
	}
	return flo_vect;
}

smm::Assertion* translate_rule(const Rule* rule, Maps& maps) {
	string rule_str = Lex::toStr(rule->id());
	uint rule_lab = Lex::toInt(rule_str);
	smm::Assertion* ra = new smm::Assertion(rule_lab);
	if (rule->vars.v.size())
		ra->variables.push_back(translate_vars(rule->vars));
	ra->floating = translate_floatings(rule->vars, maps);
	ra->prop = new smm::Proposition(true, rule_lab, translate_term(rule->term, rule->term.type.get(), maps));
	//ra->prop.axiom = true;
	//ra->prop.expr  = translate_term(rule->term, rule->type.get(), maps);
	//ra->prop.label = rule_lab;
	maps.rules[rule] = ra;
	for (auto v : rule->vars.v) {
		uint i = 0;
		for (auto& ch : rule->term.tree->children()) {
			if (ch->kind == Tree::VAR && *ch->var() == v) {
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
		string ass_str = Lex::toStr(ass->id());
		if (prop->ind)
			ass_str += "_" + to_string(prop->ind);
		uint ass_lab = Lex::toInt(ass_str);
		smm::Assertion* ra = new smm::Assertion(ass_lab);
		if (ass->vars.v.size())
			ra->variables.push_back(translate_vars(ass->vars));
		if (ass->disj.d.size())
			ra->disjointed = translate_disj(ass->disj);
		ra->floating = translate_floatings(ass->vars, maps, ass);
		ra->essential= translate_essentials(ass, maps);
		ra->prop = new smm::Proposition(false, ass_lab, translate_expr(prop->expr, maps));
		//ra->prop.expr  = translate_expr(prop->expr, maps);
		//ra->prop.label = ass_lab;
		//ra->prop.axiom = false;
		ra_vect.push_back(ra);
		maps.assertions[ass] = ra;
	}
	return ra_vect;
}

vector<smm::Node> translate_axiom(const Axiom* ax, Maps& maps) {
	vector<smm::Node> asss = translate_assertion(ax, maps);
	for (auto n : asss) {
		assert(n.type == smm::Node::ASSERTION);
		n.val.ass->prop->axiom = true;
	}
	return asss;
}

vector<smm::Node> translate_def(const Def* def, Maps& maps) {
	vector<smm::Node> asss = translate_assertion(def, maps);
	for (auto n : asss) {
		assert(n.type == smm::Node::ASSERTION);
		n.val.ass->prop->axiom = true;
	}
	return asss;
}


void translate_step(const Step* st, const Assertion* thm, vector<smm::Ref*>& smm_proof, Maps& maps);

void translate_ref(Ref* ref, const Assertion* thm, vector<smm::Ref*>& smm_proof, Maps& maps) {
	switch (ref->kind) {
	case Ref::HYP:  smm_proof.push_back(new smm::Ref(maps.essentials[thm][ref->val.hyp])); break;
	case Ref::PROP: break;
	case Ref::STEP: translate_step(ref->val.step, thm, smm_proof, maps); break;
	default : assert(false); break;
	}
}

void translate_term(const Tree& t, const Assertion* thm, vector<smm::Ref*>& smm_proof, Maps& maps) {
	if (t.kind == Tree::VAR) {
		if (maps.floatings[thm].count(*t.var()))
			smm_proof.push_back(new smm::Ref(maps.floatings[thm][*t.var()]));
		else if (maps.inners[thm].count(*t.var()))
			smm_proof.push_back(new smm::Ref(maps.inners[thm][*t.var()]));
		else
			throw Error("undeclared variable", show(*t.var()));
	} else {
		for (auto v : t.rule()->vars.v)
			translate_term(*t.children()[maps.rules_args[t.rule()][v]], thm, smm_proof, maps);
	}
	if (t.kind == Tree::NODE) {
		if (!maps.rules.count(t.rule()))
			throw Error("undefined reference to rule");
		smm_proof.push_back(new smm::Ref(maps.rules[t.rule()]->prop->label, true));
	}
}

void translate_proof(const Proof* proof, const Assertion* thm, vector<smm::Ref*>& smm_proof, Maps& maps, uint ind = 0);

void translate_step(const Step* st, const Assertion* thm, vector<smm::Ref*>& smm_proof, Maps& maps) {
	if (st->kind() == Step::CLAIM) {
		translate_proof(st->proof(), thm, smm_proof, maps);
		return;
	}
	for (auto ref : st->refs)
		translate_ref(ref, thm, smm_proof, maps);
	const Assertion* ass = st->ass();
	Substitution* ps = unify_forth(ass->props[0]->expr, st->expr);
	if (!ps) throw Error("proposition unification failed");
	for (uint i = 0; i < ass->arity(); ++ i) {
		Substitution* hs = unify_forth(ass->hyps[i]->expr, st->refs[i]->expr());
		if (!hs) throw Error("hypothesis unification failed");
		if (!ps->join(hs)) throw Error("substitution join failed");
		delete hs;
	}
	for (auto v : st->ass()->vars.v)
		translate_term(*ps->sub().at(v), thm, smm_proof, maps);
	delete ps;
	if (!maps.assertions.count(ass))
		throw Error("undefined reference to assertion");
	assert(maps.assertions.count(ass));
	smm_proof.push_back(new smm::Ref(maps.assertions[ass]->prop->label, st->ass()->kind() != Assertion::THM));
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
		smm::Inner* inn = new smm::Inner(i + ind_0);
		inn->index = i + ind_0;
		inn->expr += mdl::Symbol(maps.types[v.type()]);
		inn->expr += mdl::Symbol(v.lit, true);
		inn_vect.push_back(inn);
		smm_vars->expr.push_back(mdl::Symbol(v.lit, true));
		maps.inners[thm][v] = inn;
	}
	return inn_vect;
}

void translate_proof(const Proof* proof, const Assertion* thm, vector<smm::Ref*>& smm_proof, Maps& maps, uint ind) {
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
	vector<smm::Node> asss = translate_assertion(proof->thm, maps);
	if (proof->id() != static_cast<uint>(-1)) {
		// TODO ? WTF??
	}
	for (uint i = 0; i < asss.size(); ++ i) {
		maps.thm = asss[i].val.ass;
		maps.thm->proof = new smm::Proof();
		translate_proof(proof, proof->thm, maps.thm->proof->refs, maps, i);
	}
	join(nodes, asss);
	return nodes;
}

smm::Source* translate_source(const Source* src, Maps& maps, smm::Source* target = nullptr);

inline smm::Inclusion* translate_import(const Import* imp, Maps& maps) {
	const smm::Source* src = translate_source(imp->source.get(), maps);
	return new smm::Inclusion(src->id(), imp->primary);
}

vector<smm::Node> translate_theory(const Theory* thy, Maps& maps) {
	vector<smm::Node> nodes;
	if (maps.first_time) {
		nodes.push_back(translate_turnstile(maps));
		maps.first_time = false;
	}
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
	if (maps.sources.count(src)) {
		return maps.sources[src];
	} else {
		if (!target) {
			delete smm::Sys::get().math.get<smm::Source>().access(src->id());
			target = new smm::Source(src->id());
		}
		maps.sources[src] = target;
		target->contents = translate_theory(src->theory, maps);
		return target;
	}
}

}

smm::Source* translate(uint src, uint tgt) {
	const Source* source = Sys::get().math.get<Source>().access(src);
	if (!source) throw Error("no source", Lex::toStr(src));
	delete smm::Sys::get().math.get<smm::Source>().access(tgt);
	smm::Source* target = new smm::Source(tgt);
	Maps maps;
	maps.thm = nullptr;
	return translate_source(source, maps, target);
}

}} // mdl::rus

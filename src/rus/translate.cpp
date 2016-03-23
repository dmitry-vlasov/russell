#include "smm/ast.hpp"
#include "rus/globals.hpp"

namespace mdl { namespace rus {

struct Maps {
	map<const Assertion*, uint> assertions;
	map<const Type*, uint>      types;
	map<const Rule*, uint>      rules;
	mdl::Symbol turnstile;
};

smm::Constants* translate_turnstile(smm::Source* src, Maps& maps) {
	uint ts = Rus::mod().lex.symbs.toInt("|-");
	if (!Rus::get().math.consts.has(ts)) {
		smm::Constants* consts = new smm::Constants;
		maps.turnstile = mdl::Symbol(ts);
		consts->expr += maps.turnstile;
		return consts;
	} else
		return nullptr;
}

mdl::Expr translate_expr(const Expr& ex, Maps& maps) {
	mdl::Expr expr;
	expr += maps.turnstile;
	for (auto n : ex)
		expr += mdl::Symbol(n.symb.lit, n.symb.type);
	return expr;
}

mdl::Expr translate_term(const Expr& ex, const Type* tp, Maps& maps) {
	mdl::Expr expr;
	expr += mdl::Symbol(maps.types[tp]);
	for (auto n : ex)
		expr += mdl::Symbol(n.symb.lit, n.symb.type);
	return expr;
}

smm::Constants* translate_const(const Const* c) {
	smm::Constants* consts = new smm::Constants;
	consts->expr += mdl::Symbol(c->symb.lit);
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

void translate_type(const Type* type, smm::Source* src, Maps& maps) {
	string type_str = "ty_" + Rus::get().lex.ids.toStr(type->id);
	uint type_sy = Rus::mod().lex.symbs.toInt(type_str);
	maps.types[type] = type_sy;
	smm::Constants* consts = new smm::Constants;
	consts->expr += type_sy;
	src->contents.push_back(consts);
	for (auto p : type->supers)
		src->contents.push_back(translate_rule(p.second, maps));
}

smm::Essential* translate_hyp(const Hyp* hyp, Maps& maps) {
	smm::Essential* ess = new smm::Essential;
	ess->index = hyp->ind;
	ess->expr = translate_expr(hyp->expr, maps);
	return ess;
}

vector<smm::Floating*> translate_floating(const Vars& vars, Maps& maps) {
	vector<smm::Floating*> flo_vect;
	for (uint i = 0; i < vars.v.size(); ++ i) {
		Symbol s = vars.v[i];
		smm::Floating* flo = new smm::Floating;
		flo->index = i;
		flo->expr += mdl::Symbol(maps.types[s.type]);
		flo->expr += mdl::Symbol(s.lit, true);
		flo_vect.push_back(flo);
	}
	return flo_vect;
}

smm::Assertion* translate_rule(const Rule* rule, Maps& maps) {
	smm::Assertion* ra = new smm::Assertion();
	ra->variables.push_back(translate_vars(rule->vars));
	ra->floating = translate_floating(rule->vars, maps);
	ra->prop.axiom = true;
	ra->prop.expr  = translate_term(rule->term, rule->type, maps);
	string rule_str = "ru_" + Rus::get().lex.ids.toStr(rule->id);
	uint rule_lab = Rus::mod().lex.ids.toInt(rule_str);
	maps.rules[rule] = rule_lab;
	ra->prop.label = rule_lab;
	return ra;
}

vector<smm::Assertion*> translate_assertion(const Assertion* ass, Maps& maps) {
	vector<smm::Assertion*> ra_vect;
	for (auto prop : ass->props) {
		smm::Assertion* ra = new smm::Assertion();
		ra->variables.push_back(translate_vars(ass->vars));
		ra->floating = translate_floating(ass->vars, maps);
		for (auto hyp : ass->hyps)
			ra->essential.push_back(translate_hyp(hyp, maps));
		ra->prop.expr  = translate_expr(prop->expr, maps);
		string ass_str = "as_" + to_string(prop->ind) + "_";
		ass_str += Rus::get().lex.ids.toStr(ass->id);
		uint ass_lab = Rus::mod().lex.ids.toInt(ass_str);
		maps.assertions[ass] = ass_lab;
		ra->prop.label = ass_lab;
		ra_vect.push_back(ra);
	}
	return ra_vect;
}

vector<smm::Assertion*> translate_axiom(const Axiom* ax, Maps& maps) {
	vector<smm::Assertion*> asss = translate_assertion(&ax->ass, maps);
	for (auto ra : asss)
		ra->prop.axiom = true;
	return asss;
}

template<typename T>
void join_vectors(vector<T>& v1, const vector<T>& v2) {
	for (auto p : v2) v1.push_back(p);
}

vector<smm::Assertion*> translate_theorem(const Theorem* th, Maps& maps) {
	vector<smm::Assertion*> thms = translate_assertion(&th->ass, maps);
	/*
	for (auto ass : thms) {
		for (auto proof : th->proofs) {
			for (auto el : proof->elems) {
				if (el.kind == Proof::Elem::VARS)
					join_vectors(ass->inner, translate_floating(el.val.vars));
			}
			thms.push_back();
		}
	}*/
	return thms;
}


smm::Source* translate(const Source* source) {
	return nullptr;
}

}} // mdl::rus

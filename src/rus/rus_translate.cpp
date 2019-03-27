#include "rus_ast.hpp"
#include "mm_ast.hpp"

namespace mdl { namespace rus { namespace {

struct RuleImage {
	RuleImage(mm::Assertion* r = nullptr) : rule(r) { }
	mm::Assertion*   rule;
	map<uint, uint> args;
};

struct TypeImage {
	mm::Const* constant;
	vector<mm::Assertion*> supers;
};

struct Maps {
	struct Global {
		static uint turnstileName() {
			static uint name = Lex::toInt("turnstile_special_source"); return name;
		}
		Global() : turnstile(Lex::toInt("|-")) {
			if (!mm::Sys::get().math.get<mm::Source>().access(turnstileName())) {
				mm::Source* turnstileSource = new mm::Source(turnstileName());
				turnstileSource->contents.emplace_back(unique_ptr<mm::Const>(new mm::Const(turnstile)));
			}
		}
		map<const Const*, mm::Const*> constants;
		map<const Type*, TypeImage>    types;
		map<const Rule*, RuleImage>    rules;
		uint turnstile;
	};
	struct Local {
		Local() : thm(nullptr) { }
		map<const Assertion*, map<const Hyp*, mm::Hyp*>> essentials;
		map<const Assertion*, map<uint, mm::Var*>> floatings;
		map<const Assertion*, map<uint, mm::Var*>> inners;
		mm::Assertion* thm;
	};
	Maps() = default;
	Maps(const Global& g) : global(g) { }
	Global global;
	Local  local;
};

inline uint translate_symb(const Symbol& s) {
	switch (s.kind()) {
	case Symbol::VAR: return s.lit;
	case Symbol::CONST: {
		const Const* c = s.constant();
		return (c->ascii == -1) ? s.lit : c->ascii;
	}
	default: return s.lit;
	}
}

mm::Expr translate_expr(const Expr& ex, Maps& maps) {
	mm::Expr expr; expr.reserve(ex.symbols.size() + 1);
	expr.emplace_back(maps.global.turnstile);
	for (auto& s : ex.symbols) {
		expr.emplace_back(translate_symb(s), s.type());
	}
	return expr;
}

mm::Expr translate_term(const Expr& ex, const Type* tp) {
	mm::Expr expr; expr.reserve(ex.symbols.size() + 1);
	expr.emplace_back(tp->id());
	for (auto& s : ex.symbols) {
		expr.emplace_back(translate_symb(s), s.type());
	}
	return expr;
}

mm::Const* translate_const(const Const* c) {
	uint symb = (c->ascii == -1) ? c->id() : c->ascii;
	mm::Const* constant = new mm::Const(symb);
	return constant;
}

vector<uint> translate_vars(const Vars& rvars) {
	vector<uint> vars;
	vars.reserve(rvars.v.size());
	for (auto& s : rvars.v) {
		vars.push_back(s.lit);
	}
	return vars;
}

inline Disj::Vector translate_disj(const Disj& rdisj) {
	return rdisj.toVector();
}

RuleImage translate_rule(const Rule* rule, Maps& maps);

TypeImage translate_type(const Type* type, Maps& maps) {
	mm::Const* type_const = new mm::Const(type->id());
	vector<mm::Assertion*> type_supers;
	type_supers.reserve(type->supers.size());
	for (auto& p : type->supers) {
		RuleImage rule_image = translate_rule(p.second.get(), maps);
		maps.global.rules[p.second.get()] = rule_image;
		type_supers.push_back(rule_image.rule);
	}
	return TypeImage{type_const, type_supers};
}

vector<unique_ptr<mm::Var>> translate_floatings(const Vars& vars, Maps& maps, uint id, const Assertion* ass = nullptr);

RuleImage translate_rule(const Rule* rule, Maps& maps) {
	RuleImage image(new mm::Assertion(rule->id()));
	if (rule->vars.v.size()) {
		image.rule->vars.vars = std::move(translate_vars(rule->vars));
	}
	image.rule->outerVars = std::move(translate_floatings(rule->vars, maps, rule->id()));
	image.rule->expr = std::move(translate_term(rule->term, rule->term.type.get()));
	for (auto& v : rule->vars.v) {
		uint i = 0;
		bool found = false;
		for (auto& ch : rule->term.tree()->children()) {
			if (ch->kind() == Tree::VAR && ch->var().lit == v.lit) {
				image.args[v.lit] = i;
				found = true;
				break;
			}
			++ i;
		}
		if (!found) {
			throw Error("rule arg is not found", Lex::toStr(v.lit));
		}
	}
	return image;
}

vector<unique_ptr<mm::Hyp>> translate_essentials(const Assertion* ass, Maps& maps) {
	vector<unique_ptr<mm::Hyp>> ess_vect;
	ess_vect.reserve(ass->hyps.size());
	for (auto& hyp : ass->hyps) {
		mm::Hyp* ess = new mm::Hyp(hyp.get()->ind, ass->id());
		ess->expr = std::move(translate_expr(hyp->expr, maps));
		ess_vect.emplace_back(ess);
		maps.local.essentials[ass][hyp.get()] = ess;
	}
	return ess_vect;
}

vector<unique_ptr<mm::Var>> translate_floatings(const Vars& vars, Maps& maps, uint id, const Assertion* ass) {
	vector<unique_ptr<mm::Var>> flo_vect;
	for (uint i = 0; i < vars.v.size(); ++ i) {
		const Symbol& v = vars.v[i];
		mm::Var* flo = new mm::Var(false, i, id, v.type()->id(), v.lit);
		flo_vect.emplace_back(flo);
		if (ass) {
			maps.local.floatings[ass][v.lit] = flo;
		}
	}
	return flo_vect;
}

vector<mm::Assertion*> translate_assertion(const Assertion* ass, Maps& maps) {
	vector<mm::Assertion*> image;
	image.reserve(ass->props.size());
	for (auto& p : ass->props) {
		const Prop* prop = p.get();
		string ass_str = Lex::toStr(ass->id());
		if (prop->ind) {
			ass_str += "_" + to_string(prop->ind);
		}
		uint ass_lab = Lex::toInt(ass_str);
		mm::Assertion* ra = new mm::Assertion(ass_lab);
		if (ass->vars.v.size()) {
			ra->vars.vars = std::move(translate_vars(ass->vars));
		}
		if (ass->disj.dvars.size()) {
			ra->disj.vect = std::move(translate_disj(ass->disj));
		}
		ra->outerVars = std::move(translate_floatings(ass->vars, maps, ass->id(), ass));
		ra->hyps = std::move(translate_essentials(ass, maps));
		ra->expr = std::move(translate_expr(prop->expr, maps));
		image.push_back(ra);
	}
	return image;
}

inline vector<mm::Assertion*> translate_axiom(const Axiom* ax, Maps& maps) {
	return translate_assertion(ax, maps);
}

inline vector<mm::Assertion*> translate_def(const Def* def, Maps& maps) {
	return translate_assertion(def, maps);
}

void translate_step(const Step* st, const Assertion* thm, vector<mm::Ref>& proof, Maps& maps);

void translate_ref(Ref* ref, const Assertion* thm, vector<mm::Ref>& mm2_proof, Maps& maps) {
	switch (ref->kind()) {
	case Ref::HYP:  mm2_proof.emplace_back(maps.local.essentials[thm][ref->hyp()]); break;
	case Ref::PROP: break;
	case Ref::STEP: translate_step(ref->step(), thm, mm2_proof, maps); break;
	default : assert(false); break;
	}
}

void translate_term(const Tree& t, const Assertion* thm, vector<mm::Ref>& proof, Maps& maps) {
	if (t.kind() == Tree::VAR) {
		if (maps.local.floatings[thm].count(t.var().lit)) {
			proof.emplace_back(maps.local.floatings[thm][t.var().lit]);
		} else if (maps.local.inners[thm].count(t.var().lit)) {
			proof.emplace_back(maps.local.inners[thm][t.var().lit]);
		} else {
			throw Error("undeclared variable", show(t.var()));
		}
	} else {
		for (auto& v : t.rule()->vars.v) {
			RuleImage rule = maps.global.rules.at(t.rule());
			translate_term(*t.children()[rule.args[v.lit]].get(), thm, proof, maps);
		}
	}
	if (t.kind() == Tree::RULE) {
		if (!maps.global.rules.count(t.rule())) {
			throw Error("undefined reference to rule");
		}
		proof.emplace_back(maps.global.rules.at(t.rule()).rule->id());
	}
}

void translate_proof(const Proof* proof, const Assertion* thm, vector<mm::Ref>& mm_proof, Maps& maps, uint ind = 0);

void translate_step(const Step* st, const Assertion* thm, vector<mm::Ref>& proof, Maps& maps) {
	if (st->kind() == Step::CLAIM) {
		translate_proof(st->proof(), thm, proof, maps);
		return;
	}
	const Assertion* ass = st->ass();
	if (!st->sub) {
		string msg;
		msg += st->show();
		throw Error("proof step unification failure", msg);
	}
	for (auto& v : ass->vars.v) {
		translate_term(st->sub.sub().at(v.lit), thm, proof, maps);
	}
	for (const auto& ref : st->refs) {
		translate_ref(ref.get(), thm, proof, maps);
	}
	proof.emplace_back(ass->id());
}

vector<unique_ptr<mm::Var>> translate_inners(const Vars& vars, Maps& maps, const Assertion* thm, uint ind_0) {
	vector<unique_ptr<mm::Var>> inn_vect;
	for (uint i = 0; i < vars.v.size(); ++ i) {
		const Symbol& v = vars.v[i];
		mm::Var* inn = new mm::Var(true, i + ind_0, thm->id(), v.type()->id(), v.lit);
		inn_vect.emplace_back(inn);
		maps.local.thm->vars.vars.push_back(v.lit);
		maps.local.inners[thm][v.lit] = inn;
	}
	return inn_vect;
}

void translate_proof(const Proof* proof, const Assertion* thm, vector<mm::Ref>& mm_proof, Maps& maps, uint ind) {
	maps.local.thm->innerVars = std::move(translate_inners(proof->allvars, maps, thm, maps.local.thm->innerVars.size()));
	for (const auto& el : proof->elems) {
		if (Proof::kind(el) == Proof::QED && Proof::qed(el)->prop->ind == ind) {
			translate_step(Proof::qed(el)->step, thm, mm_proof, maps);
			break;
		}
	}
}

vector<mm::Assertion*> translate_proof(const Proof* proof, Maps& maps) {
	vector<mm::Assertion*> asss = std::move(translate_assertion(proof->thm.get(), maps));
	if (proof->id() != static_cast<uint>(-1)) {
		// TODO ? WTF??
	}
	for (uint i = 0; i < asss.size(); ++ i) {
		maps.local.thm = asss[i];
		translate_proof(proof, proof->thm.get(), maps.local.thm->proof.refs, maps, i);
	}
	return asss;
}

inline void add_turnstile(vector<mm::Source::Node>& nodes) {
	nodes.emplace_back(unique_ptr<mm::Import>(new mm::Import(Maps::Global::turnstileName())));
}

inline void add_const(vector<mm::Source::Node>& nodes, const Const* c, Maps& maps) {
	nodes.emplace_back(unique_ptr<mm::Const>(maps.global.constants.at(c)));
}

inline void add_type(vector<mm::Source::Node>& nodes, const Type* t, Maps& maps) {
	TypeImage image = maps.global.types.at(t);
	nodes.emplace_back(unique_ptr<mm::Const>(image.constant));
	for (auto r : image.supers) {
		nodes.emplace_back(unique_ptr<mm::Assertion>(r));
	}
}

inline void add_rule(vector<mm::Source::Node>& nodes, const Rule* r, Maps& maps) {
	nodes.emplace_back(unique_ptr<mm::Assertion>(maps.global.rules.at(r).rule));
}

inline void add_assertion(vector<mm::Source::Node>& nodes, const Assertion* a, Maps& maps) {
	for (auto ass : translate_assertion(a, maps)) {
		nodes.emplace_back(unique_ptr<mm::Assertion>(ass));
	}
}

inline void add_proof(vector<mm::Source::Node>& nodes, const Proof* p, Maps& maps) {
	for (auto ass : translate_proof(p, maps)) {
		nodes.emplace_back(unique_ptr<mm::Assertion>(ass));
	}
}

inline void add_import(vector<mm::Source::Node>& nodes, const Import* i) {
	nodes.emplace_back(unique_ptr<mm::Import>(new mm::Import(i->source.id())));
}

inline void add_comment(vector<mm::Source::Node>& nodes, const Comment* c) {
	nodes.emplace_back(unique_ptr<mm::Comment>(new mm::Comment(c->text)));
}

vector<mm::Source::Node> translate_theory(const Theory* thy, Maps& maps);

inline void add_theory(vector<mm::Source::Node>& nodes, const Theory* t, Maps& maps) {
	vector<mm::Source::Node> image = translate_theory(t, maps);
	std::move(std::begin(image), std::end(image), std::back_inserter(nodes));
}

vector<mm::Source::Node> translate_theory(const Theory* thy, Maps& maps) {
	vector<mm::Source::Node> nodes;
	add_turnstile(nodes);
	for (auto& n : thy->nodes) {
		switch (Theory::kind(n)) {
		case Theory::CONST:   add_const(nodes, Theory::const_(n), maps); break;
		case Theory::TYPE:    add_type(nodes, Theory::type(n), maps);   break;
		case Theory::RULE:    add_rule(nodes, Theory::rule(n), maps);  break;

		case Theory::AXIOM:   add_assertion(nodes, Theory::axiom(n), maps);  break;
		case Theory::DEF:     add_assertion(nodes, Theory::def(n), maps); break;
		case Theory::THEOREM: break;  // theorem is translated implicitly in proof
		case Theory::PROOF:   add_proof(nodes, Theory::proof(n), maps);  break;
		case Theory::THEORY:  add_theory(nodes, Theory::theory(n), maps); break;
		case Theory::IMPORT:  add_import(nodes, Theory::import(n));       break;
		case Theory::COMMENT: add_comment(nodes, Theory::comment(n));      break;
		default : assert(false && "impossible"); break;
		}
	}
	return nodes;
}

mm::Source* translate_source(uint src, Maps maps, uint tgt = -1) {
	tgt = (tgt == -1) ? src : tgt;
	const rus::Source* source = Sys::get().math.get<Source>().access(src);
	mm::Source* target = mm::Sys::mod().math.get<mm::Source>().access(tgt);
	if (target) {
		delete target;
	}
	target = new mm::Source(tgt);
	target->contents = std::move(translate_theory(&source->theory, maps));
	return target;
}

static void find_dependencies(uint src, set<uint>& deps, set<uint>& visited) {
	visited.insert(src);
	const Source* source = Sys::get().math.get<Source>().access(src);
	for (const auto& n : source->theory.nodes) {
		if (Theory::kind(n) == Theory::IMPORT) {
			uint imp = Theory::import(n)->source.id();
			if (!visited.count(imp)) {
				find_dependencies(imp, deps, visited);
			}
			const mm::Source* inpTarg = mm::Sys::mod().math.get<mm::Source>().access(imp);
			const Source* inpSrc = Sys::get().math.get<Source>().access(imp);
			if (inpSrc->has_changed() || !inpTarg) {
				deps.insert(imp);
			}
		}
	}
}

static vector<uint> find_dependencies(uint src) {
	set<uint> visited;
	set<uint> deps;
	find_dependencies(src, deps, visited);
	vector<uint> ret;
	ret.reserve(deps.size());
	for (uint s : deps) ret.push_back(s);
	return ret;
}

Maps::Global translate_global() {
	Maps maps;
	for (auto& p : Sys::get().math.get<Const>()) {
		const Const* c = p.second.data;
		maps.global.constants[c] = translate_const(c);
	}
	for (auto& p : Sys::get().math.get<Type>()) {
		const Type* t = p.second.data;
		maps.global.types[t] = translate_type(t, maps);
	}
	for (auto& p : Sys::get().math.get<Rule>()) {
		const Rule* r = p.second.data;
		if (!maps.global.rules.count(r)) {
			maps.global.rules[r] = translate_rule(r, maps);
		}
	}
	return maps.global;
}

}

#ifdef PARALLEL
#define PARALLEL_RUS_TRANSLATE
#endif

mm::Source* translate(uint src, uint tgt) {
	const Source* source = Sys::get().math.get<Source>().access(src);
	if (!source) throw Error("no source", Lex::toStr(src));
	Maps::Global global = translate_global();
	vector<uint> deps = find_dependencies(src);
#ifdef PARALLEL_RUS_TRANSLATE
	tbb::parallel_for (tbb::blocked_range<size_t>(0, deps.size()),
		[deps, global] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				translate_source(deps[i], Maps(global));
			}
		}
	);
#else
	for (uint s : deps) {
		translate_source(s, Maps(global));
	}
#endif
	return translate_source(src, Maps(global), tgt);
}

}} // mdl::rus

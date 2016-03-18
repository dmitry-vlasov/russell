#include "smm/tree.hpp"
#include "rus/ast.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm { namespace {

struct Maps {
	map<const Assertion*, rus::Assertion*> assertions;
	map<uint, rus::Type*> types;
	rus::Type*            wff;
};

static void translate_const(const Expr& consts, rus::Theory& target) {
	for (auto s : consts.symbols) {
		rus::Const* c = new rus::Const{rus::Symbol(s), rus::Symbol(), rus::Symbol()};
		target.nodes.push_back(rus::Node(c));
	}
}

inline bool is_turnstile(Symbol s) {
	return s.lit == Smm::mod().lex.symbols.toInt("|-");
}
inline bool is_def(uint label) {
	return Smm::get().lex.labels.toStr(label).substr(0,4) == "def-";
}
inline uint equiv_sy() {
	return Smm::mod().lex.symbols.toInt("<->");
}
inline uint equal_sy() {
	return Smm::mod().lex.symbols.toInt("=");
}

static rus::Expr translate_expr(const Expr& e, Maps& maps) {
	rus::Expr ex(e);
	// it's the best what we can do here ...
	ex.type = maps.wff;
	return ex;
}

template<typename T>
static rus::Vars translate_vars(vector<T*> decls, Maps& maps) {
	rus::Vars rus_vars;
	for (auto flo : decls) {
		if (maps.types.find(flo->type().lit) == maps.types.end())
			throw Error("unknown type", show_sy(flo->type()));
		rus::Type* type = maps.types[flo->type().lit];
		rus_vars.v.push_back(rus::Symbol(flo->var(), true, type));
	}
	return rus_vars;
}

static rus::Disj translate_disj(const Assertion* ass, Maps& maps) {
	rus::Disj rus_disj;
	for (auto dis : ass->disjointed) {
		rus_disj.d.push_back(vector<rus::Symbol>());
		for (auto v : dis->expr.symbols) {
			if (maps.types.find(v.lit) == maps.types.end())
				throw Error("unknown type", show_sy(v));
			rus::Type* type = maps.types[v.lit];
			rus_disj.d.back().push_back(rus::Symbol(v.lit, true, type));
		}
	}
	return rus_disj;
}

static rus::Type* translate_type(uint type_lit, rus::Theory& target, Maps& maps) {
	string type_str = Smm::get().lex.symbols.toStr(type_lit);
	uint type_id = Smm::mod().lex.labels.toInt(type_str);
	if (maps.types.find(type_lit) == maps.types.end()) {
		rus::Type* type = new rus::Type { type_id };
		maps.types[type_lit] = type;
		target.nodes.push_back(type);
		if (type_str == "wff")
			maps.wff = type;
		return type;
	} else
		return maps.types.find(type_lit)->second;
}

static void translate_rule(const Assertion* ass, rus::Theory& target, Maps& maps) {
	rus::Rule* rule = new rus::Rule {
		ass->prop.label,
		translate_type(ass->prop.expr[0].lit, target, maps),
		translate_vars(ass->floating, maps),
		rus::Expr(ass->prop.expr)
	};
	target.nodes.push_back(rule);
}

template<class T>
void translate_assertion(const Assertion* ass, T* a, Maps& maps) {
	a->ass.id = ass->prop.label;
	a->ass.vars = translate_vars(ass->floating, maps);
	a->ass.disj = translate_disj(ass, maps);
	uint hc = 0;
	for (auto ess : ass->essential) {
		rus::Expr ex = translate_expr(ess->expr, maps);
		a->ass.hyps.push_back(new rus::Hyp{hc++, ex});
	}
	rus::Expr ex = translate_expr(ass->prop.expr, maps);
	a->ass.props.push_back(new rus::Prop{0, ex});
}

static void translate_axiom(const Assertion* ass, rus::Theory& target, Maps& maps) {
	rus::Axiom* ax = new rus::Axiom;
	translate_assertion<rus::Axiom>(ass, ax, maps);
	target.nodes.push_back(ax);
	maps.assertions[ass] = &ax->ass;
}

static void translate_def(const Assertion* ass, rus::Theory& target, Maps& maps) {


	rus::Axiom* ax = new rus::Axiom;
	translate_assertion<rus::Axiom>(ass, ax, maps);
	target.nodes.push_back(ax);
}

rus::Node::Kind ass_kind(const Assertion* ass) {
	if (!is_turnstile(ass->prop.expr.symbols.front())) {
		return rus::Node::RULE;
	} else if (is_def(ass->prop.label)) {
		return rus::Node::DEF;
	} else if (!ass->proof) {
		return rus::Node::AXIOM;
	} else {
		return rus::Node::THEOREM;
	}
}

static rus::Ref translate_ref(Ref ref, vector<rus::Ref>& proof, rus::Theorem* thm, Maps& maps) {
	switch (ref.type) {
	case Ref::ESSENTIAL:
		return rus::Ref(thm->ass.hyps[ref.val.ess->index]);
	case Ref::FLOATING:  return rus::Ref();
	case Ref::INNER:	 return rus::Ref();
	case Ref::PROOF: {
		rus::Ref sr(new rus::Step());
		Assertion* ass = ref.val.prf->refs.back().val.ass;
		sr.val.step->ass = maps.assertions.find(ass)->second;
		for (uint i = 0; i < ass->essential.size(); ++ i) {
			rus::Ref hr = translate_ref(ref.val.prf->refs[i], proof, thm, maps);
			sr.val.step->refs.push_back(hr);
		}
		sr.val.step->ind = proof.size();
		sr.val.step->expr = translate_expr(ref.expr, maps);
		switch (ass_kind(ass)) {
		case rus::Node::AXIOM:   sr.val.step->kind = rus::Step::AX; break;
		case rus::Node::DEF:     sr.val.step->kind = rus::Step::DF; break;
		case rus::Node::THEOREM: sr.val.step->kind = rus::Step::TH; break;
		default : assert(false && "impossible"); break;
		}
		proof.push_back(sr);
		return sr;
	}
	default : assert(false && "impossible"); break;
	}
	return rus::Ref(); // pacifying compiler
}

static void translate_proof(const Assertion* ass, rus::Theorem* thm, rus::Theory& target, Maps& maps) {
	Ref tree = Ref(to_tree(ass->proof));
	eval(tree);
	rus::Proof* p = new rus::Proof();
	p->vars = translate_vars(ass->inner, maps);
	p->theorem = &thm->ass;
	translate_ref(tree, p->steps, thm, maps);
	rus::Prop* pr = thm->ass.props.front();
	rus::Step* st = p->steps.back().val.step;
	p->steps.push_back(new rus::Qed{pr, st});
	target.nodes.push_back(p);
	tree.destroy();
}

static void translate_theorem(const Assertion* ass, rus::Theory& target, Maps& maps) {
	rus::Theorem* thm = new rus::Theorem;
	translate_assertion<rus::Theorem>(ass, thm, maps);
	target.nodes.push_back(thm);
	translate_proof(ass, thm, target, maps);
	maps.assertions[ass] = &thm->ass;
}

static void translate_ass(const Assertion* ass, rus::Theory& target, Maps& maps) {
	switch (ass_kind(ass)) {
	case rus::Node::RULE    : translate_rule(ass, target, maps);    break;
	case rus::Node::DEF     : translate_def(ass, target, maps);     break;
	case rus::Node::AXIOM   : translate_axiom(ass, target, maps);   break;
	case rus::Node::THEOREM : translate_theorem(ass, target, maps); break;
	default : assert(false && "impossible"); break;
	}
}

static void translate_node(const Node& node, rus::Theory& target, Maps& maps) {
	switch(node.type) {
	case Node::CONSTANTS: translate_const(node.val.cst->expr, target); break;
	case Node::ASSERTION: translate_ass(node.val.ass, target, maps);   break;
	case Node::SOURCE:
		// TODO:
		//translate(node.val.blk, target);
		break;
	default : assert(false && "impossible"); break;
	}
}

static void translate_theory(const Source* source, rus::Theory& target, Maps& maps) {
	for (auto n : source->contents)
		translate_node(n, target, maps);
}

} // anonymous namespace

rus::Source* translate_to_rus(const Source* source) {
	rus::Source* target = new rus::Source(Smm::get().config.out);
	Maps maps;
	maps.wff = nullptr;
	translate_theory(source, target->theory, maps);
	return target;
}

}} // mdl::smm

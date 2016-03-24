#include "smm/tree.hpp"
#include "rus/ast.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm { namespace {

struct Maps {
	map<const Assertion*, rus::Axiom*>   axioms;
	map<const Assertion*, rus::Theorem*> theorems;
	map<const Assertion*, rus::Def*>     defs;
	map<Symbol, rus::Type*> types;
	rus::Type*              wff;
	set<Symbol>             redundant_consts;
};

static void translate_const(const Expr& consts, rus::Theory& target, const Maps& maps) {
	for (auto s : consts.symbols) {
		rus::Const* c = new rus::Const{rus::Symbol(s), rus::Symbol(), rus::Symbol()};
		if (maps.redundant_consts.find(s) == maps.redundant_consts.end())
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
		rus_vars.v.push_back(rus::Symbol(flo->var(), type, true));
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
			rus_disj.d.back().push_back(rus::Symbol(v.lit, type, true));
		}
	}
	return rus_disj;
}

static rus::Type* translate_type(Symbol type_sy, rus::Theory& target, Maps& maps) {
	if (maps.types.find(type_sy) == maps.types.end()) {
		string type_str = Smm::get().lex.symbols.toStr(type_sy.lit);
		uint type_id = Smm::mod().lex.labels.toInt(type_str);
		rus::Type* type = new rus::Type { type_id };
		maps.types[type_sy] = type;
		target.nodes.push_back(type);
		if (type_str == "wff")
			maps.wff = type;
		return type;
	} else
		return maps.types.find(type_sy)->second;
}

inline bool rule_term_is_super(const Expr& term) {
	return term.symbols.size() == 2 && !term.symbols[0].var && term.symbols[1].var;
}

static void translate_super(const Assertion* ass, rus::Theory& target, Maps& maps) {
	Symbol super_sy = ass->prop.expr[0];
	Symbol infer_sy = ass->floating[0]->type();
	assert(ass->prop.expr[1] == ass->floating[0]->var());
	rus::Type* super = translate_type(super_sy, target, maps);
	rus::Type* infer = translate_type(infer_sy, target, maps);
	infer->sup.push_back(super);
}

static void translate_rule(const Assertion* ass, rus::Theory& target, Maps& maps) {
	if (rule_term_is_super(ass->prop.expr)) {
		translate_super(ass, target, maps);
		return;
	}
	rus::Rule* rule = new rus::Rule {
		ass->prop.label,
		translate_type(ass->prop.expr[0], target, maps),
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
	maps.axioms[ass] = ax;
}

static void translate_def(const Assertion* ass, rus::Theory& target, Maps& maps) {


	rus::Axiom* ax = new rus::Axiom;
	translate_assertion<rus::Axiom>(ass, ax, maps);
	target.nodes.push_back(ax);
	maps.axioms[ass] = ax;
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

static rus::Proof::Elem translate_step(Ref ref, rus::Proof* proof, rus::Theorem* thm, Maps& maps) {
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
			hr = rus::Ref(translate_step(r, proof, thm, maps).val.step);
		}
		el.val.step->refs.push_back(hr);
	}
	el.val.step->ind = elems.size();
	el.val.step->expr = translate_expr(ref.expr, maps);
	switch (ass_kind(ass)) {
	case rus::Node::AXIOM:
		el.val.step->val.axm = maps.axioms.find(ass)->second;
		el.val.step->kind = rus::Step::AXM; break;
	case rus::Node::DEF:
		el.val.step->val.def = maps.defs.find(ass)->second;
		el.val.step->kind = rus::Step::DEF; break;
	case rus::Node::THEOREM:
		el.val.step->val.thm = maps.theorems.find(ass)->second;
		el.val.step->kind = rus::Step::THM; break;
	default : assert(false && "impossible"); break;
	}
	elems.push_back(el);
	return el;
}

static void translate_proof(const Assertion* ass, rus::Theorem* thm, rus::Theory& target, Maps& maps) {
	Ref tree = Ref(to_tree(ass->proof));
	eval(tree);
	rus::Proof* p = new rus::Proof();
	p->vars = translate_vars(ass->inner, maps);
	p->thm = thm;
	translate_step(tree, p, thm, maps);
	rus::Prop* pr = thm->ass.props.front();
	rus::Step* st = p->elems.back().val.step;
	p->elems.push_back(new rus::Qed{pr, st});
	target.nodes.push_back(p);
	tree.destroy();
}

static void translate_theorem(const Assertion* ass, rus::Theory& target, Maps& maps) {
	rus::Theorem* thm = new rus::Theorem;
	translate_assertion<rus::Theorem>(ass, thm, maps);
	target.nodes.push_back(thm);
	translate_proof(ass, thm, target, maps);
	maps.theorems[ass] = thm;
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
	case Node::CONSTANTS: translate_const(node.val.cst->expr, target, maps); break;
	case Node::ASSERTION: translate_ass(node.val.ass, target, maps); break;
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
	maps.redundant_consts.insert(Smm::get().lex.symbols.getInt("wff"));
	maps.redundant_consts.insert(Smm::get().lex.symbols.getInt("set"));
	maps.redundant_consts.insert(Smm::get().lex.symbols.getInt("class"));
	maps.redundant_consts.insert(Smm::get().lex.symbols.getInt("|-"));
	translate_theory(source, target->theory, maps);
	return target;
}

}} // mdl::smm

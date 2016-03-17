#include "smm/tree.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm {

struct Maps {
	map<const smm::Assertion*, rus::Theorem*> theorems;
	map<const smm::Assertion*, rus::Axiom*>   axioms;
	map<const smm::Assertion*, rus::Rule*>    rules;
	map<const smm::Assertion*, rus::Def*>     defs;
	map<const smm::Proof*,     rus::Proof*>   proofs;
	//Transform                            transform;
	map<uint, rus::Type*>                     types;
};

static void translate_const(const Expr& consts, rus::Theory& target) {
	for (auto s : consts.symbols) {
		rus::Const* c = new rus::Const { s, Symbol(), Symbol() };
		target.nodes.push_back(rus::Node(c));
	}
}

inline bool is_turnstile(Symbol s) {
	return s.lit == Smm::mod().lex.symbols.toInt("|-");
}
inline bool is_def(uint label) {
	return Smm::get().lex.labels.toStr(label).substr(0,4) == "def-";
}

static rus::Vars translate_vars(const Assertion* ass, Maps& maps) {
	rus::Vars rus_vars;
	for (auto flo : ass->floating) {
		if (maps.types.find(flo->type().lit) == maps.types.end())
			throw Error("unknown type");
		rus::Type* type = maps.types[flo->type().lit];
		rus_vars.v.push_back(rus::Symbol(flo->var(), true, type));
	}
	return rus_vars;
}

static rus::Type* translate_type(uint type_lit, rus::Theory& target, Maps& maps) {
	string type_str = Smm::get().lex.symbols.toStr(type_lit);
	uint type_id = Smm::mod().lex.labels.toInt(type_str);
	if (maps.types.find(type_id) == maps.types.end()) {
		rus::Type* type = new rus::Type { type_id };
		maps.types[type_id] = type;
		target.nodes.push_back(type);
		return type;
	} else
		return maps.types.find(type_id)->second;
}

static void translate_rule(const Assertion* ass, rus::Theory& target, Maps& maps) {
	rus::Rule* rule = new rus::Rule {
		ass->prop.label,
		translate_type(ass->prop.expr[0].lit, target, maps),
		translate_vars(ass, maps),
		ass->prop.expr
	};
	target.nodes.push_back(rule);
}

static void translate_axiom(const Assertion* ass, rus::Theory& target, Maps& maps) {
	rus::Axiom* ax = new rus::Axiom;
	ax->ass.id = ass->prop.label;
	ax->ass.vars = translate_vars(ass, maps);
	//ax->ass.disj = translate_disj(ass);
	uint hc = 0;
	for (auto ess : ass->essential) {
		ax->ass.hyps.push_back(new rus::Hyp{hc++, rus::Expr(ess->expr)});
	}
	ax->ass.props.push_back(new rus::Prop{0, rus::Expr(ass->prop.expr)});
	target.nodes.push_back(ax);
}

static void translate_def(const Assertion* ass, rus::Theory& target, Maps& maps) {
	return translate_axiom(ass, target, maps);
}

static void translate_theorem(const Assertion* ass, rus::Theory& target, Maps& maps) {

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
	case Node::CONSTANTS:
		translate_const(node.val.cst->expr, target);
		break;
	case Node::ASSERTION:
		translate_ass(node.val.ass, target, maps);
		break;
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

rus::Source* translate_to_rus(const Source* source) {
	rus::Source* target = new rus::Source(Smm::get().config.out);
	Maps maps;
	translate_theory(source, target->theory, maps);
	return target;
}

}} // mdl::smm

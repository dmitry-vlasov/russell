#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "mm/globals.hpp"

namespace mdl { namespace mm {

static void gather_expr_vars(set<Symbol>& vars, const Expr& expr) {
	for (Symbol s : expr.symbols)
		if (s.var) vars.insert(s);
}

static void gather_inner_vars(const set<Symbol>& fvars,
	set<Symbol>& ivars, set<Symbol>& avars, const Proof* proof) {
	if (!proof) return;
	for (Node n : proof->refs) {
		if (n.type == Node::FLOATING) {
			Symbol v = n.val.flo->var();
			avars.insert(v);
			if (fvars.find(v) == fvars.end())
				ivars.insert(v);
		}
	}
}

typedef map<uint, uint> Reindex;

// Replace variable sets with single set, which contains only needed variables.
//
static void reduce_variables(smm::Assertion* ass, const set<Symbol>& needed) {
	Expr rvars;
	for (const smm::Variables& vars : ass->variables) {
		for (Symbol v : vars.expr.symbols) {
			if (needed.find(v) != needed.end())
				rvars += v;
		}
	}
	ass->variables.clear();
	ass->variables.push_back(smm::Variables { rvars });
}

// Remove floatings, which variable is not needed.
//
static void reduce_floatings(smm::Assertion* ass, const set<Symbol>& needed, Reindex& reindex) {
	vector<smm::Floating> red_flos;
	uint i = 0;
	for (auto& flo : ass->floating) {
		if (needed.find(flo.var()) != needed.end()) {
			reindex[flo.index] = i;
			flo.index = i++;
			red_flos.push_back(flo);
		}
	}
	ass->floating = red_flos;
}

// Reindex essentials.
//
static void reindex_essentials(smm::Assertion* ass, Reindex& reindex) {
	uint i = 0;
	for (auto& ess : ass->essential) {
		reindex[ess.index] = i;
		ess.index = i++;
	}
}

static smm::Proof* translate(Proof* mproof, Reindex& reindex) {
	typedef smm::Ref::Type RType;
	smm::Proof* sproof = new smm::Proof();
	for (auto& node : mproof->refs) {
		smm::Ref sref;
		Node::Value val = node.val;
		switch (node.type) {
		case Node::FLOATING:  sref = smm::Ref { RType::PREF_F, reindex[val.flo->label] }; break;
		case Node::ESSENTIAL: sref = smm::Ref { RType::PREF_E, reindex[val.ess->label] }; break;
		case Node::AXIOM:     sref = smm::Ref { RType::PREF_A, val.ax->label };  break;
		case Node::THEOREM:   sref = smm::Ref { RType::PREF_P, val.th->label };  break;
		default : assert(false && "impossible"); break;
		}
		sproof->refs.push_back(sref);
	}
	return sproof;
}


static void reduce(smm::Assertion* ass, Proof* proof = nullptr) {
	// Gather the variables, used in assertion hypotheses and statement (header).
	set<Symbol> flo_vars;
	for (auto& ess : ass->essential) {
		gather_expr_vars(flo_vars, ess.expr);
	}
	gather_expr_vars(flo_vars, ass->prop.expr);

	// Gather the variables, used in proof but not in header, and collect all vars.
	set<Symbol> inn_vars;
	set<Symbol> all_vars(flo_vars);
	gather_inner_vars(flo_vars, inn_vars, all_vars, proof);

	Reindex reindex;
	reduce_variables(ass, all_vars);
	reduce_floatings(ass, flo_vars, reindex);
	reindex_essentials(ass, reindex);
	if (proof) {
		ass->proof = translate(proof, reindex);
	}
}

static void gather(uint ind, const Block* block, smm::Assertion* ass) {
	deque<Variables*>  vars;
	deque<Disjointed*> disj;
	deque<Floating*>   flos;
	deque<Essential*>  esss;
	for (int i = ind - 1; i >= 0; -- i) {
		switch (block->contents[i].type) {
		case Node::VARIABLES:  vars.push_front(block->contents[i].val.var); break;
		case Node::DISJOINTED: disj.push_front(block->contents[i].val.dis); break;
		case Node::FLOATING:   flos.push_front(block->contents[i].val.flo); break;
		case Node::ESSENTIAL:  esss.push_front(block->contents[i].val.ess); break;
		default : break;
		}
	}
	if (block->parent) gather(block->ind, block->parent, ass);
	for (auto var : vars) ass->variables.push_back(smm::Variables { var->expr });
	for (auto dis : disj) ass->disjointed.push_back(smm::Disjointed { dis->expr });
	for (auto flo : flos) ass->floating.push_back(smm::Floating {flo->label, flo->expr });
	for (auto ess : esss) ass->essential.push_back(smm::Essential {ess->label, ess->expr });
}

static void translate(const Block* source, Target* target);

static void translate(const Node& node, const Block* block, Target* target) {
	switch(node.type) {
	case Node::NONE: assert(false && "impossible"); break;;
	case Node::CONSTANTS: {
		smm::Constants* c = new smm::Constants { node.val.cst->expr };
		target->contents.push_back(smm::Node(c));
	} break;
	case Node::VARIABLES:  break;
	case Node::DISJOINTED: break;
	case Node::FLOATING:   break;
	case Node::ESSENTIAL:  break;
	case Node::AXIOM: {
		smm::Assertion* ass = new smm::Assertion();
		ass->prop = smm::Proposition { true, node.val.ax->label, node.val.ax->expr };
		gather(node.ind, block, ass);
		reduce(ass);
		target->contents.push_back(smm::Node(ass));
	} break;
	case Node::THEOREM: {
		smm::Assertion* th = new smm::Assertion();
		th->prop = smm::Proposition { false, node.val.th->label, node.val.th->expr };
		gather(node.ind, block, th);
		reduce(th, node.val.th->proof);
		target->contents.push_back(smm::Node(th));
	}	break;
	case Node::BLOCK:
		node.val.blk->ind = node.ind;
		translate(node.val.blk, target);
		break;
	default : assert(false && "impossible"); break;
	}
}

static void translate(const Block* source, Target* target) {
	for (auto& node : source->contents)
		translate(node, source, target);
}

Target* translate(const Block* source) {
	Target* target = new smm::Source(Mm::get().config.out);
	translate(source, target);
	return target;
}

}} // mdl::mm


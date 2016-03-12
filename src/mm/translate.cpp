#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "mm/globals.hpp"

namespace mdl { namespace mm {

void mark_expr_vars(const Variables& vars, const Expr& expr) {
	//for (Symbol& s : expr.symbols)
	//	if (vars.expr.contains(s)) s.var = true;
}

void mark_expr_vars(const Block* block, const Expr& expr) {
	/*for (Symbol& s : expr.symbols) {
		const Block* b = block;
		while (b) {
			if (b->vars.expr.contains(s)) s.var = true;
			b = b->parent;
		}
	}*/
}

void gather_expr_vars(set<Symbol>& vars, const Expr& expr) {
	for (Symbol s : expr.symbols)
		if (s.var) vars.insert(s);
}

void gather_inner_vars(const set<Symbol>& fvars,
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

// Replace variable sets with single set, which contains only needed variables.
//
void reduce_variables(smm::Assertion* ass, const set<Symbol>& needed) {
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
void reduce_floatings(smm::Assertion* ass, const set<Symbol>& needed) {
	vector<smm::Floating> red_flos;
	for (auto& flo : ass->floating) {
		if (needed.find(flo.var()) != needed.end())
			red_flos.push_back(flo);
	}
	ass->floating = red_flos;
}

void reduce(smm::Assertion* ass, Proof* proof = nullptr) {
	// Gather the variables, used in assertion hypotheses and statement (header).
	set<Symbol> flo_vars;
	for (auto& ess : ass->essential) {
		gather_expr_vars(flo_vars, ess.expr);
	}
	gather_expr_vars(flo_vars, ass->prop.expr);

	for (auto s : flo_vars) {
		cout << s << ", ";
	}
	cout << endl;

	// Gather the variables, used in proof but not in header, and collect all vars.
	set<Symbol> inn_vars;
	set<Symbol> all_vars(flo_vars);
	gather_inner_vars(flo_vars, inn_vars, all_vars, proof);

	reduce_variables(ass, all_vars);
	reduce_floatings(ass, flo_vars);
}

smm::Proof* translate(Proof* mproof) {
	typedef smm::Ref::Type RType;
	smm::Proof* sproof = new smm::Proof();
	for (auto& node : mproof->refs) {
		smm::Ref sref;
		Node::Value val = node.val;
		switch (node.type) {
		case Node::FLOATING:  sref = smm::Ref { RType::PREF_F, val.flo->label }; break;
		case Node::ESSENTIAL: sref = smm::Ref { RType::PREF_E, val.ess->label }; break;
		case Node::AXIOM:     sref = smm::Ref { RType::PREF_A, val.ax->label };  break;
		case Node::THEOREM:   sref = smm::Ref { RType::PREF_P, val.th->label };  break;
		default : assert(false && "impossible"); break;
		}
		sproof->refs.push_back(sref);
	}
	return sproof;
}

void gather(uint ind, const Block* block, smm::Assertion* ass) {
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

void translate(const Block* source, Target* target);

void translate(const Node& node, const Block* block, Target* target) {
	switch(node.type) {
	case Node::NONE: assert(false && "impossible"); break;;
	case Node::CONSTANTS: {
		smm::Constants* c = new smm::Constants { node.val.cst->expr };
		target->contents.push_back(smm::Node(c));
	} break;
	case Node::VARIABLES: {
		//for (Symbol v : node.val.var->expr.symbols)
		//	block->vars.insert(v);
	}	break;
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
		th->proof = translate(node.val.th->proof);
		target->contents.push_back(smm::Node(th));
	}	break;
	case Node::BLOCK:
		node.val.blk->ind = node.ind;
		translate(node.val.blk, target);
		break;
	default : assert(false && "impossible"); break;
	}
}

void translate(const Block* source, Target* target) {
	for (auto& node : source->contents)
		translate(node, source, target);
}

Target* translate(const Block* source) {
	Target* target = new smm::Source(Mm::get().config.out);
	translate(source, target);
	return target;
}

}} // mdl::mm


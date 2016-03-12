#include "mm/ast.hpp"
#include "smm/ast.hpp"
#include "mm/globals.hpp"

namespace mdl { namespace mm {

smm::Proof* translate(Proof* proof) {
	return nullptr;
}

void gather(uint ind, const Block* block, smm::Assertion* ass) {
	deque<Variables*>  vars;
	deque<Disjointed*> disj;
	deque<Floating*>   flos;
	deque<Essential*>  esss;
	for (int i = ind - 1; i > 0; -- i) {
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
	for (auto flo : flos) ass->floating.push_back(smm::Floating {0, flo->expr });
	for (auto ess : esss) ass->essential.push_back(smm::Essential {0, ess->expr });
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
		ass->prop = smm::Proposition { true, 0, node.val.ax->expr };
		gather(node.ind, block, ass);
		target->contents.push_back(smm::Node(ass));
	} break;
	case Node::THEOREM: {
		smm::Assertion* th = new smm::Assertion();
		th->prop = smm::Proposition { false, 0, node.val.th->expr };
		gather(node.ind, block, th);
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


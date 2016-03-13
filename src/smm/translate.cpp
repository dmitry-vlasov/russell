#include "smm/ast.hpp"
#include "smm/tree.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm {

struct Maps {
	map<uint, mm::Theorem*>   theorems;
	map<uint, mm::Axiom*>     axioms;
	map<uint, mm::Essential*> essentials;
	map<uint, mm::Floating*>  floatings;
	map<uint, mm::Floating*>  inners;
	tree::Transform           transform;
};

static mm::Proof* translate(const Maps& maps, const Proof* proof) {
	Tree* tree = to_tree(proof);
	transform(tree, maps.transform);
	Proof* rpn = to_rpn(tree);
	mm::Proof* pr = new mm::Proof();
	for (auto& ref : rpn->refs) {
		mm::Node node;
		switch (ref.type) {
		case Ref::PREF_A: node = mm::Node(maps.axioms.find(ref.index)->second);     break;
		case Ref::PREF_P: node = mm::Node(maps.theorems.find(ref.index)->second);   break;
		case Ref::PREF_F: node = mm::Node(maps.floatings.find(ref.index)->second);  break;
		case Ref::PREF_I: node = mm::Node(maps.inners.find(ref.index)->second);     break;
		case Ref::PREF_E: node = mm::Node(maps.essentials.find(ref.index)->second); break;
		default : assert(false && "impossible"); break;
		}
		pr->refs.push_back(node);
	}
	delete rpn;
	delete tree;
	return pr;
}

static tree::Perm create_permutation(uint flos, uint esss) {
	tree::Perm perm;
	for (uint i = 0; i < esss; ++ i)
		perm[i] = i + flos;
	for (uint i = 0; i < flos; ++ i)
		perm[i + esss] = i;
	return perm;
}

static void translate(const Node& node, mm::Block* target, Maps& maps) {
	switch(node.type) {
	case Node::NONE: assert(false && "impossible"); break;;
	case Node::CONSTANTS: {
		mm::Constants* c = new mm::Constants { node.val.cst->expr };
		target->contents.push_back(mm::Node(c));
	} break;
	case Node::ASSERTION: {
		mm::Block* block = new mm::Block();
		const Assertion* ass = node.val.ass;
		string name = Smm::get().lex.labels.toStr(ass->prop.label);
		for (auto& vars : ass->variables)
			block->contents.push_back(mm::Node(new mm::Variables { vars.expr }));
		for (auto& disj : ass->disjointed)
			block->contents.push_back(mm::Node(new mm::Disjointed { disj.expr }));
		for (auto& inn : ass->inner) {
			string label = "i" + name + "_" + to_string(inn.index);
			uint new_index = Smm::mod().lex.labels.toInt(label);
			mm::Floating* mm_flo = new mm::Floating { new_index, inn.expr };
			block->contents.push_back(mm::Node(mm_flo));
			maps.inners[inn.index] = mm_flo;
		}
		for (auto& flo : ass->floating) {
			string label = "f" + name + "_" + to_string(flo.index);
			uint new_index = Smm::mod().lex.labels.toInt(label);
			mm::Floating* mm_flo = new mm::Floating { new_index, flo.expr };
			block->contents.push_back(mm::Node(mm_flo));
			maps.floatings[flo.index] = mm_flo;
		}
		for (auto& ess : ass->essential) {
			string label = "e" + name + "_" + to_string(ess.index);
			uint new_index = Smm::mod().lex.labels.toInt(label);
			mm::Essential* mm_ess = new mm::Essential { new_index, ess.expr };
			block->contents.push_back(mm::Node(mm_ess));
			maps.essentials[ess.index] = mm_ess;
		}
		if (ass->proof) {
			mm::Proof* pr = translate(maps, ass->proof);
			mm::Theorem* th = new mm::Theorem();
			th->label = ass->prop.label;
			th->expr = ass->prop.expr;
			th->proof = pr;
			block->contents.push_back(mm::Node(th));
			maps.theorems[ass->prop.label] = th;
		} else {
			mm::Axiom* ax = new mm::Axiom { ass->prop.label, ass->prop.expr };
			block->contents.push_back(mm::Node(ax));
			maps.axioms[ass->prop.label] = ax;
		}
		block->parent = target;
		target->contents.push_back(mm::Node(block));
		tree::Perm perm = create_permutation(
			ass->floating.size(),
			ass->essential.size()
		);
		maps.transform[ass->prop.label] = perm;
	}	break;
	case Node::SOURCE:
		// TODO:
		//translate(node.val.blk, target);
		break;
	default : assert(false && "impossible"); break;
	}
}


static void translate(const Source* source, mm::Block* target) {
	Maps maps;
	for (auto& node : source->contents)
		translate(node, target, maps);
}

mm::Block* translate_to_mm(const Source* source) {
	mm::Block* target = new mm::Block(Smm::get().config.out);
	translate(source, target);
	return target;
}

}} // mdl::smm

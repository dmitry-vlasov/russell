#include "smm/sys.hpp"
#include "smm/tree.hpp"

namespace mdl { namespace smm { namespace {

struct Maps {
	map<const smm::Assertion*, mm::Theorem*>   theorems;
	map<const smm::Assertion*, mm::Axiom*>     axioms;
	map<const smm::Essential*, mm::Essential*> essentials;
	map<const smm::Floating*,  mm::Floating*>  floatings;
	map<const smm::Inner*,     mm::Floating*>  inners;
	map<const smm::Source*,    mm::Source*>    sources;
	Transform                            transform;
};

mm::Proof* translate(Maps& maps, const Proof* proof) {
	Proof* tree = to_tree(proof);
	transform(tree, maps.transform);
	Proof* rpn = to_rpn(tree);
	mm::Proof* pr = new mm::Proof();
	for (auto r : rpn->refs) {
		mm::Ref* ref = nullptr;
		switch (r->type) {
		case Ref::AXIOM:     ref = new mm::Ref(maps.axioms[r->val.ass]->label);     break;
		case Ref::THEOREM:   ref = new mm::Ref(maps.theorems[r->val.ass]->label);   break;
		case Ref::FLOATING:  ref = new mm::Ref(maps.floatings[r->val.flo]->label);  break;
		case Ref::INNER:     ref = new mm::Ref(maps.inners[r->val.inn]->label);     break;
		case Ref::ESSENTIAL: ref = new mm::Ref(maps.essentials[r->val.ess]->label); break;
		default : assert(false && "impossible"); break;
		}
		pr->refs.push_back(ref);
	}
	delete rpn;
	delete tree;
	return pr;
}

Perm create_permutation(uint flos, uint esss) {
	Perm perm;
	for (uint i = 0; i < esss; ++ i)
		perm[i] = i + flos;
	for (uint i = 0; i < flos; ++ i)
		perm[i + esss] = i;
	return perm;
}

mm::Source* translate_source(const Source* src, Maps& maps, mm::Source* target = nullptr);

void translate(const Node& node, mm::Block* target, Maps& maps) {
	switch(node.type) {
	case Node::CONSTANTS: {
		mm::Constants* c = new mm::Constants { node.val.cst->expr };
		target->contents.push_back(mm::Node(c));
	} break;
	case Node::ASSERTION: {
		mm::Block* block = new mm::Block();
		const Assertion* ass = node.val.ass;
		string name = Lex::toStr(ass->prop.label);
		for (auto& vars : ass->variables)
			block->contents.push_back(mm::Node(new mm::Variables { vars->expr }));
		for (auto& disj : ass->disjointed)
			block->contents.push_back(mm::Node(new mm::Disjointed { disj->expr }));
		for (auto& inn : ass->inner) {
			string label = "i" + name + "_" + to_string(inn->index);
			uint new_index = Lex::toInt(label);
			mm::Floating* mm_flo = new mm::Floating { new_index, inn->expr };
			block->contents.push_back(mm::Node(mm_flo));
			maps.inners[inn] = mm_flo;
		}
		for (auto& flo : ass->floating) {
			string label = "f" + name + "_" + to_string(flo->index);
			uint new_index = Lex::toInt(label);
			mm::Floating* mm_flo = new mm::Floating { new_index, flo->expr };
			block->contents.push_back(mm::Node(mm_flo));
			maps.floatings[flo] = mm_flo;
		}
		for (auto& ess : ass->essential) {
			string label = "e" + name + "_" + to_string(ess->index);
			uint new_index = Lex::toInt(label);
			mm::Essential* mm_ess = new mm::Essential { new_index, ess->expr };
			block->contents.push_back(mm::Node(mm_ess));
			maps.essentials[ess] = mm_ess;
		}
		if (ass->proof) {
			mm::Proof* pr = translate(maps, ass->proof);
			mm::Theorem* th = new mm::Theorem(ass->prop.label, ass->prop.expr, pr);
			block->contents.push_back(mm::Node(th));
			assert(!maps.theorems.count(ass));
			maps.theorems[ass] = th;
		} else {
			mm::Axiom* ax = new mm::Axiom { ass->prop.label, ass->prop.expr };
			block->contents.push_back(mm::Node(ax));
			assert(!maps.axioms.count(ass));
			maps.axioms[ass] = ax;
		}
		block->parent = target;
		target->contents.push_back(mm::Node(block));
		Perm perm = create_permutation(
			ass->floating.size(),
			ass->essential.size()
		);
		maps.transform[ass->prop.label] = perm;
	}	break;
	case Node::INCLUSION: {
		mm::Source* s = translate_source(node.val.inc->source, maps);
		mm::Inclusion* i = new mm::Inclusion(s, node.val.inc->primary);
		target->contents.push_back(mm::Node(i));
	} 	break;
	case Node::COMMENT: {
		mm::Comment* c = new mm::Comment(node.val.com->text);
		target->contents.push_back(mm::Node(c));
	} 	break;
	default : assert(false && "impossible"); break;
	}
}


mm::Source* translate_source(const Source* src, Maps& maps, mm::Source* target) {
	if (maps.sources.count(src)) {
		return maps.sources[src];
	} else {
		if (!target) {
			target = new mm::Source(src->label);
			target->block = new mm::Block;
		}
		maps.sources[src] = target;
		for (auto& node : src->contents)
			translate(node, target->block, maps);
		return target;
	}
}

}

void translate_to_mm(uint src, uint tgt) {
	const Source* source = Sys::get().math.sources.access(src);
	mm::Source* target = new mm::Source(tgt);
	target->block = new mm::Block;
	Maps maps;
	translate_source(source, maps, target);
}

}} // mdl::smm

#include "smm/tree.hpp"
#include "smm/globals.hpp"

namespace mdl { namespace smm { namespace {

struct Maps {
	Map<const smm::Assertion*, mm::Theorem*>   theorems;
	Map<const smm::Assertion*, mm::Axiom*>     axioms;
	Map<const smm::Essential*, mm::Essential*> essentials;
	Map<const smm::Floating*,  mm::Floating*>  floatings;
	Map<const smm::Inner*,     mm::Floating*>  inners;
	Map<const smm::Source*,    mm::Source*>    sources;
	Transform                            transform;
};

mm::Proof* translate(const Maps& maps, const Proof* proof) {
	Proof* tree = to_tree(proof);
	transform(tree, maps.transform);
	Proof* rpn = to_rpn(tree);
	mm::Proof* pr = new mm::Proof();
	for (auto& r : rpn->refs) {
		mm::Ref ref;
		switch (r.type) {
		case Ref::AXIOM:     ref = mm::Ref(maps.axioms[r.val.ass]);     break;
		case Ref::THEOREM:   ref = mm::Ref(maps.theorems[r.val.ass]);   break;
		case Ref::FLOATING:  ref = mm::Ref(maps.floatings[r.val.flo]);  break;
		case Ref::INNER:     ref = mm::Ref(maps.inners[r.val.inn]);     break;
		case Ref::ESSENTIAL: ref = mm::Ref(maps.essentials[r.val.ess]); break;
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
		string name = Smm::get().lex.labels.toStr(ass->prop.label);
		for (auto& vars : ass->variables)
			block->contents.push_back(mm::Node(new mm::Variables { vars->expr }));
		for (auto& disj : ass->disjointed)
			block->contents.push_back(mm::Node(new mm::Disjointed { disj->expr }));
		for (auto& inn : ass->inner) {
			string label = "i" + name + "_" + to_string(inn->index);
			uint new_index = Smm::mod().lex.labels.toInt(label);
			mm::Floating* mm_flo = new mm::Floating { new_index, inn->expr };
			block->contents.push_back(mm::Node(mm_flo));
			maps.inners[inn] = mm_flo;
		}
		for (auto& flo : ass->floating) {
			string label = "f" + name + "_" + to_string(flo->index);
			uint new_index = Smm::mod().lex.labels.toInt(label);
			mm::Floating* mm_flo = new mm::Floating { new_index, flo->expr };
			block->contents.push_back(mm::Node(mm_flo));
			maps.floatings[flo] = mm_flo;
		}
		for (auto& ess : ass->essential) {
			string label = "e" + name + "_" + to_string(ess->index);
			uint new_index = Smm::mod().lex.labels.toInt(label);
			mm::Essential* mm_ess = new mm::Essential { new_index, ess->expr };
			block->contents.push_back(mm::Node(mm_ess));
			maps.essentials[ess] = mm_ess;
		}
		if (ass->proof) {
			mm::Proof* pr = translate(maps, ass->proof);
			mm::Theorem* th = new mm::Theorem();
			th->label = ass->prop.label;
			th->expr = ass->prop.expr;
			th->proof = pr;
			block->contents.push_back(mm::Node(th));
			assert(!maps.theorems.has(ass));
			maps.theorems[ass] = th;
		} else {
			mm::Axiom* ax = new mm::Axiom { ass->prop.label, ass->prop.expr };
			block->contents.push_back(mm::Node(ax));
			assert(!maps.axioms.has(ass));
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
	case Node::INCLUSION:{
		mm::Source* s = translate_source(node.val.inc->source, maps);
		mm::Inclusion* i = new mm::Inclusion(s, node.val.inc->primary);
		target->contents.push_back(mm::Node(i));
	} 	break;
	default : assert(false && "impossible"); break;
	}
}


mm::Source* translate_source(const Source* src, Maps& maps, mm::Source* target) {
	if (maps.sources.has(src)) {
		return maps.sources[src];
	} else {
		Config conf = Smm::get().config;
		if (!target)
			target = new mm::Source(
				conf.deep ? conf.out : conf.root,
				src->name
			);
		maps.sources[src] = target;
		for (auto& node : src->contents)
			translate(node, target->block, maps);
		return target;
	}
}

}

mm::Source* translate_to_mm(const Source* source) {
	Config conf = Smm::get().config;
	mm::Source* target = new mm::Source(
		conf.deep ? conf.out : conf.root,
		conf.deep ? conf.in  : conf.out
	);
	Maps maps;
	return translate_source(source, maps, target);
}

}} // mdl::smm

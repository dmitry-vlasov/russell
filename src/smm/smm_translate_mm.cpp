#include <mm_ast.hpp>
#include <smm_ast.hpp>
#include "smm_tree.hpp"

namespace mdl { namespace smm { namespace {



struct Maps {
	map<const smm::Assertion*, mm::Theorem*>   theorems;
	map<const smm::Assertion*, mm::Axiom*>     axioms;
	map<const smm::Essential*, mm::Essential*> essentials;
	map<const smm::Floating*,  mm::Floating*>  floatings;
	map<const smm::Inner*,     mm::Floating*>  inners;
	map<const smm::Source*,    mm::Source*>    sources;
	set<uint>                                  variables;
	Transform                                  transform;
};

mm::Proof* translate(Maps& maps, const Proof* proof) {
	Tree* tree = to_tree(proof);
	transform(tree, maps.transform);
	Proof* rpn = to_proof(tree);
	mm::Proof* pr = new mm::Proof();
	for (auto r : rpn->refs) {
		mm::Ref* ref = nullptr;
		switch (r->type()) {
		case Ref::AXIOM:     ref = new mm::Ref(maps.axioms[r->ass()]->id());     break;
		case Ref::THEOREM:   ref = new mm::Ref(maps.theorems[r->ass()]->id());   break;
		case Ref::FLOATING:  ref = new mm::Ref(maps.floatings[r->flo()]->id());  break;
		case Ref::INNER:     ref = new mm::Ref(maps.inners[r->inn()]->id());     break;
		case Ref::ESSENTIAL: ref = new mm::Ref(maps.essentials[r->ess()]->id()); break;
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

mm::Expr translate_expr(const Expr& e) {
	mm::Expr ex; ex.reserve(e.size());
	for (auto s : e) ex.emplace_back(uint(s.lit));
	return ex;
}

mm::Source* translate_source(const Source* src, Maps& maps, mm::Source* target = nullptr);

void translate(const Node& node, mm::Block* target, Maps& maps) {
	switch(node.type) {
	case Node::CONSTANT: {
		mm::Constant* c = new mm::Constant(uint(node.val.cst->symb.lit));
		target->contents.emplace_back(c);
	} break;
	case Node::ASSERTION: {
		mm::Block* block = new mm::Block();
		const Assertion* ass = node.val.ass;
		string name = Lex::toStr(ass->prop->label);
		for (const auto& vars : ass->variables) {
			for (const auto& var : vars->expr) {
				if (maps.variables.find(var.lit) == maps.variables.end()) {
					auto smm_var = new mm::Variable(var.lit);
					target->contents.emplace_back(smm_var);
					maps.variables.insert(var.lit);
				}
			}
		}
		for (auto& disj : ass->disjointed)
			block->contents.emplace_back(new mm::Disjointed(std::move(translate_expr(disj->expr))));
		for (auto& inn : ass->inner) {
			string label = "i" + name + "_" + to_string(inn->index);
			uint new_index = Lex::toInt(label);
			mm::Floating* mm_flo = new mm::Floating(new_index, std::move(translate_expr(inn->expr)));
			block->contents.emplace_back(mm_flo);
			maps.inners[inn] = mm_flo;
		}
		for (auto& flo : ass->floating) {
			string label = "f" + name + "_" + to_string(flo->index);
			uint new_index = Lex::toInt(label);
			mm::Floating* mm_flo = new mm::Floating(new_index, std::move(translate_expr(flo->expr)));
			block->contents.emplace_back(mm_flo);
			maps.floatings[flo] = mm_flo;
		}
		for (auto& ess : ass->essential) {
			string label = "e" + name + "_" + to_string(ess->index);
			uint new_index = Lex::toInt(label);
			mm::Essential* mm_ess = new mm::Essential(new_index, std::move(translate_expr(ess->expr)));
			block->contents.emplace_back(mm_ess);
			maps.essentials[ess] = mm_ess;
		}
		if (ass->proof) {
			mm::Proof* pr = translate(maps, ass->proof);
			mm::Theorem* th = new mm::Theorem(ass->prop->label, std::move(translate_expr(ass->prop->expr)), pr);
			block->contents.emplace_back(th);
			assert(!maps.theorems.count(ass));
			maps.theorems[ass] = th;
		} else {
			mm::Axiom* ax = new mm::Axiom(ass->prop->label, std::move(translate_expr(ass->prop->expr)));
			block->contents.emplace_back(ax);
			assert(!maps.axioms.count(ass));
			maps.axioms[ass] = ax;
		}
		block->parent = target;
		target->contents.emplace_back(block);
		Perm perm = create_permutation(
			ass->floating.size(),
			ass->essential.size()
		);
		maps.transform[ass->prop->label] = perm;
	}	break;
	case Node::INCLUSION: {
		mm::Source* s = translate_source(node.val.inc->source.get(), maps);
		mm::Inclusion* i = new mm::Inclusion(s->id(), node.val.inc->primary);
		target->contents.emplace_back(i);
	} 	break;
	case Node::COMMENT: {
		mm::Comment* c = new mm::Comment(node.val.com->text);
		target->contents.emplace_back(c);
	} 	break;
	default : assert(false && "impossible"); break;
	}
}

mm::Source* translate_source(const Source* src, Maps& maps, mm::Source* target) {
	if (maps.sources.count(src)) {
		return maps.sources[src];
	} else {
		if (!target) {
			delete mm::Sys::get().math.get<mm::Source>().access(src->id());
			target = new mm::Source(src->id());
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
	const Source* source = Sys::get().math.get<Source>().access(src);
	if (!source) throw Error("no source", Lex::toStr(src));
	delete mm::Sys::get().math.get<mm::Source>().access(tgt);
	mm::Source* target = new mm::Source(tgt);
	target->block = new mm::Block;
	Maps maps;
	translate_source(source, maps, target);
}

}} // mdl::smm

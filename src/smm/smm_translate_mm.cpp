#include <mm_ast.hpp>
#include <smm_ast.hpp>
#include "smm_tree.hpp"

namespace mdl { namespace smm { namespace {

inline uint translate_floating_id(const Floating* flo, const Assertion* ass) {
	return Lex::toInt(string("f") + Lex::toStr(ass->id()) + "_" + to_string(flo->index));
}

inline uint translate_essential_id(const Essential* ess, const Assertion* ass) {
	return Lex::toInt(string("e") + Lex::toStr(ass->id()) + "_" + to_string(ess->index));
}

inline uint translate_inner_id(const Inner* inn, const Assertion* ass) {
	return Lex::toInt(string("i") + Lex::toStr(ass->id()) + "_" + to_string(inn->index));
}

mm::Proof* translate(const Proof* proof) {
	Tree* tree = to_tree(proof);
	transform(tree);
	Proof* rpn = to_proof(tree);
	mm::Proof* pr = new mm::Proof();
	for (auto r : rpn->refs) {
		mm::Ref* ref = nullptr;
		switch (r->type()) {
		case Ref::AXIOM:     ref = new mm::Ref(r->ass()->id()); break;
		case Ref::THEOREM:   ref = new mm::Ref(r->ass()->id()); break;
		case Ref::FLOATING:  ref = new mm::Ref(translate_floating_id(r->flo(), proof->theorem));  break;
		case Ref::INNER:     ref = new mm::Ref(translate_inner_id(r->inn(), proof->theorem));     break;
		case Ref::ESSENTIAL: ref = new mm::Ref(translate_essential_id(r->ess(), proof->theorem)); break;
		default : assert(false && "impossible"); break;
		}
		pr->refs.push_back(ref);
	}
	delete rpn;
	delete tree;
	return pr;
}

mm::Expr translate_expr(const Expr& e) {
	mm::Expr ex; ex.reserve(e.size());
	for (auto s : e) ex.emplace_back(uint(s.lit));
	return ex;
}

void translate(const Node& node, mm::Block* target) {
	switch(node.type) {
	case Node::CONSTANT: {
		target->contents.emplace_back(new mm::Constant(uint(node.val.cst->symb.lit)));
	} break;
	case Node::ASSERTION: {
		mm::Block* block = new mm::Block();
		const Assertion* ass = node.val.ass;
		string name = Lex::toStr(ass->prop->label);
		for (const auto& vars : ass->variables) {
			for (const auto& var : vars->expr) {
				block->contents.emplace_back(new mm::Variable(var.lit));
			}
		}
		for (auto& disj : ass->disjointed) {
			block->contents.emplace_back(new mm::Disjointed(std::move(translate_expr(disj->expr))));
		}
		for (auto& inn : ass->inner) {
			block->contents.emplace_back(new mm::Floating(translate_inner_id(inn, ass), std::move(translate_expr(inn->expr))));
		}
		for (auto& flo : ass->floating) {
			block->contents.emplace_back(new mm::Floating(translate_floating_id(flo, ass), std::move(translate_expr(flo->expr))));
		}
		for (auto& ess : ass->essential) {
			block->contents.emplace_back(new mm::Essential(translate_essential_id(ess, ass), std::move(translate_expr(ess->expr))));
		}
		if (ass->proof) {
			mm::Proof* pr = translate(ass->proof);
			block->contents.emplace_back(new mm::Theorem(ass->prop->label, std::move(translate_expr(ass->prop->expr)), pr));
		} else {
			block->contents.emplace_back(new mm::Axiom(ass->prop->label, std::move(translate_expr(ass->prop->expr))));
		}
		block->parent = target;
		target->contents.emplace_back(block);
	}	break;
	case Node::INCLUSION: {
		target->contents.emplace_back(new mm::Inclusion(node.val.inc->source.id(), node.val.inc->primary));
	} 	break;
	case Node::COMMENT: {
		target->contents.emplace_back(new mm::Comment(node.val.com->text));
	} 	break;
	default : assert(false && "impossible"); break;
	}
}

mm::Source* translate_source(uint src, uint tgt = -1) {
	tgt = (tgt == -1) ? src : tgt;
	const smm::Source* source = Sys::get().math.get<Source>().access(src);
	mm::Source* target = mm::Sys::mod().math.get<mm::Source>().access(tgt);
	if (target) {
		delete target;
	}
	target = new mm::Source(tgt);
	target->block = new mm::Block;
	for (const auto& node : source->contents) {
		translate(node, target->block);
	}
	return target;
}

static void find_dependencies(uint src, set<uint>& deps, set<uint>& visited) {
	visited.insert(src);
	const Source* source = Sys::get().math.get<Source>().access(src);
	for (const auto& n : source->contents) {
		if (n.type == Node::INCLUSION) {
			uint inc = n.val.inc->source.id();
			if (!visited.count(inc)) {
				find_dependencies(inc, deps, visited);
			}
			const mm::Source* incTarg = mm::Sys::mod().math.get<mm::Source>().access(inc);
			const Source* incSrc = Sys::get().math.get<Source>().access(inc);
			if (incSrc->has_changed() || !incTarg) {
				deps.insert(inc);
			}
		}
	}
}

static vector<uint> find_dependencies(uint src) {
	set<uint> visited;
	set<uint> deps;
	find_dependencies(src, deps, visited);
	vector<uint> ret;
	ret.reserve(deps.size());
	for (uint s : deps) ret.push_back(s);
	return ret;
}

}

#define PARALLEL_TRANSLATE

mm::Source* translate_to_mm(uint src, uint tgt) {
	const Source* source = Sys::get().math.get<Source>().access(src);
	if (!source) throw Error("no source", Lex::toStr(src));
	vector<uint> deps = find_dependencies(src);
#ifdef PARALLEL_TRANSLATE
	tbb::parallel_for (tbb::blocked_range<size_t>(0, deps.size()),
		[deps] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				translate_source(deps[i]);
			}
		}
	);
#else
	for (uint s : deps) {
		translate_source(s);
	}
#endif
	return translate_source(src, tgt);
}


}} // mdl::smm

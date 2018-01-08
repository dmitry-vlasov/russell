#include <smm_ast.hpp>
#include "smm_tree.hpp"

namespace mdl { namespace smm {

typedef map<uint, uint> Perm;
typedef map<uint, Perm> Transform;
typedef map<Symbol, Expr> Subst;


Tree* to_tree(const Proof* proof) {
	stack<Tree*> stack;
	for (Ref* r : proof->refs) {
		switch(r->type()) {
		case Ref::ESSENTIAL:
		case Ref::FLOATING:
		case Ref::INNER:
			stack.push(new Tree(r));
			break;
		case Ref::AXIOM:
		case Ref::THEOREM: {
			Tree* t = new Tree();
			t->nodes.push_back(r);
			for (uint i = 0; i < r->ass()->arity(); ++ i) {
				t->nodes.push_back(stack.top());
				stack.pop();
			}
			std::reverse(t->nodes.begin(), t->nodes.end());
			stack.push(t);
		}	break;
		default : assert(false && "impossible"); break;
		}
	}
	Tree* tree = stack.top();
	stack.pop();
	if (!stack.empty())
		throw Error("non-empty stack at the end of the proof");
	return tree;
}

static void to_proof(const Tree* t, vector<Ref*>& proof) {
	for (auto n : t->nodes) {
		switch(n.type) {
		case Tree::Node::REF:
			proof.push_back(new Ref(*n.val.ref));
			break;
		case Tree::Node::TREE:
			to_proof(n.val.tree, proof);
			break;
		default : assert(false && "impossible"); break;
		}
	}
}

Proof* to_proof(const Tree* tree) {
	Proof* proof = new Proof();
	to_proof(tree, proof->refs);
	return proof;
}

void transform(Tree* tree, const Transform& trans, bool forward) {
	for (uint i = 0; i < tree->nodes.size() - 1; ++ i) {
		if (tree->nodes[i].type == Tree::Node::TREE)
			transform(tree->nodes[i].val.tree, trans, forward);
	}
	assert(tree->nodes.back().type == Tree::Node::REF);
	Ref* op = tree->nodes.back().val.ref;
	if (op->is_assertion()) {
		Perm perm = trans.at(op->label());
		assert(perm.size() + 1 == tree->nodes.size());
		vector<Tree::Node> new_nodes = tree->nodes;
		for (uint i = 0; i < new_nodes.size() - 1; ++ i) {
			if (forward) new_nodes[perm[i]] = tree->nodes[i];
			else         new_nodes[i] = tree->nodes[perm[i]];
		}
		tree->nodes = new_nodes;
	}
}

Expr eval(Tree* proof);

Expr eval(Tree::Node& n) {
	if (!n.expr.size()) {
		switch (n.type) {
		case Tree::Node::TREE: n.expr = eval(n.val.tree); break;
		case Tree::Node::REF: {
			Ref* ref = n.val.ref;
			switch (ref->type()) {
			case Ref::ESSENTIAL: n.expr = ref->ess()->expr; break;
			case Ref::FLOATING:  n.expr = ref->flo()->expr; break;
			case Ref::INNER:	 n.expr = ref->inn()->expr; break;
			default : assert(false && "impossible");
			}
		}}
	}
	return n.expr;
}

Expr eval(Tree* tree) {
	Tree::Node& n = tree->nodes.back();
	if (n.expr.size()) return n.expr;
	assert(n.type == Tree::Node::REF);
	Ref* ref = n.val.ref;
	if (!ref->is_assertion()) return eval(n);
	const Assertion* ass = ref->ass();
	Subst sub;
	uint flo_ind = 0, esss = ass->essential.size();
	for (auto flo : ass->floating) {
		Tree::Node& f = tree->nodes[esss + flo_ind ++];
		sub[flo->var()] = eval(f);
	}
	uint ess_ind = 0;
	for (auto ess : ass->essential) {
		if (apply_subst(sub, ess->expr) != eval(tree->nodes[ess_ind ++])) {
			string msg = "hypothesis mismatch:\n";
			msg += show_ex(apply_subst(sub, ess->expr)) + "\n";
			msg += "and\n";
			msg += show_ex(eval(tree->nodes[ess_ind])) + "\n";
			msg += "assertion " + Lex::toStr(ass->prop->label) + "\n";
			throw Error("verification", msg);
		}
	}
	n.expr = apply_subst(sub, ass->prop->expr);
	return n.expr;
}

}} // mdl::smm



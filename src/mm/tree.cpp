#include "mm/ast.hpp"
#include "mm/tree.hpp"

#include "mm/sys.hpp"

namespace mdl { namespace mm {

Tree* to_tree(const Proof* proof) {
	stack<Tree*> stack;
	for (auto r : proof->refs) {
		switch(r->type) {
		case Ref::ESSENTIAL:
		case Ref::FLOATING:
			stack.push(new Tree(r));
			break;
		case Ref::AXIOM:
		case Ref::THEOREM: {
			Tree* t = new Tree();
			t->nodes.push_back(r);
			for (uint i = 0; i < r->arity(); ++ i) {
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

void transform(Tree* tree, Transform& trans, bool forward) {
	for (uint i = 0; i < tree->nodes.size() - 1; ++ i) {
		if (tree->nodes[i].type == Tree::Node::TREE)
			transform(tree->nodes[i].val.tree, trans);
	}
	assert(tree->nodes.back().type == Tree::Node::REF);
	Ref* op = tree->nodes.back().val.ref;
	Perm perm = trans[op->label()];
	assert(perm.size() + 1 == tree->nodes.size());
	vector<Tree::Node> new_nodes = tree->nodes;
	for (uint i = 0; i < new_nodes.size() - 1; ++ i) {
		if (forward) new_nodes[perm[i]] = tree->nodes[i];
		else         new_nodes[i] = tree->nodes[perm[i]];
	}
	tree->nodes = new_nodes;
}

Tree* reduce(Tree* tree, const set<uint>& red) {
	assert(tree->nodes.back().type == Tree::Node::REF);
	if (red.count(tree->nodes.back().val.ref->label())) {
		assert(tree->nodes[tree->nodes.size() - 2].type == Tree::Node::TREE);
		Tree* t = nullptr;
		std::swap(tree->nodes[tree->nodes.size() - 2].val.tree, t);
		delete tree;
		return reduce(t, red);
	} else {
		for (auto& n : tree->nodes)
			if (n.type == Tree::Node::TREE)
				n.val.tree = reduce(n.val.tree, red);
		return tree;
	}
}

}} // mdl::mm



#include <boost/range/adaptor/reversed.hpp>

#include "smm/ast.hpp"
#include "smm/tree.hpp"

namespace mdl { namespace smm {

Proof* to_tree(const Proof* proof) {
	stack<Ref> stack;
	for (auto r : proof->refs) {
		switch(r.type) {
		case Ref::ESSENTIAL:
		case Ref::FLOATING:
		case Ref::INNER:
			stack.push(r); break;
		case Ref::AXIOM:
		case Ref::THEOREM: {
			Proof* tree = new Proof(Proof::TREE);
			tree->refs.push_back(r);
			for (uint i = 0; i < r.val.ass->arity(); ++ i) {
				tree->refs.push_back(stack.top());
				stack.pop();
			}
			std::reverse(tree->refs.begin(), tree->refs.end());
			stack.push(Ref(tree));
		}	break;
		default : assert(false && "impossible"); break;
		}
	}
	Proof* tree = stack.top().val.prf;
	stack.pop();
	assert(stack.empty());
	return tree;
}

static void to_rpn(const Proof* tree, vector<Ref>& proof) {
	for (auto& r : tree->refs) {
		if (r.type == Ref::PROOF)
			to_rpn(r.val.prf, proof);
		else
			proof.push_back(r);
	}
}

Proof* to_rpn(const Proof* tree) {
	Proof* rpn = new Proof();
	vector<Ref>& proof = rpn->refs;
	to_rpn(tree, proof);
	return rpn;
}

void transform(Proof* tree, const Transform& trans, bool forward) {
	for (uint i = 0; i + 1 < tree->refs.size(); ++ i) {
		if (tree->refs[i].type == Ref::PROOF)
			transform(tree->refs[i].val.prf, trans);
	}
	Ref op = tree->refs.back();
	Perm perm = trans.find(op.label())->second;
	assert(perm.size() + 1 == tree->refs.size());
	vector<Ref> new_refs = tree->refs;
	for (uint i = 0; i < new_refs.size() - 1; ++ i)
		if (forward) new_refs[perm[i]] = tree->refs[i];
		else         new_refs[i] = tree->refs[perm[i]];
	tree->refs = new_refs;
}

}} // mdl::mm



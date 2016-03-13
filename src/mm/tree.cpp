#include <boost/range/adaptor/reversed.hpp>

#include "mm/ast.hpp"
#include "mm/tree.hpp"

namespace mdl { namespace mm {

Proof* to_tree(const Proof* proof) {
	stack<Node> stack;
	for (auto n : proof->refs) {
		switch(n.type) {
		case Node::ESSENTIAL:
		case Node::FLOATING:
		//case Node::PROOF:
			stack.push(n);
			break;
		case Node::AXIOM:
		case Node::THEOREM: {
			Proof* p = new Proof();
			p->tree = true;
			p->refs.push_back(n);
			for (uint i = 0; i < ass_arity(n); ++ i) {
				p->refs.push_back(stack.top());
				stack.pop();
			}
			std::reverse(p->refs.begin(), p->refs.end());
			stack.push(Node(p));
		}	break;
		default : assert(false && "impossible"); break;
		}
	}
	Proof* tree = stack.top().val.prf;
	stack.pop();
	assert(stack.empty());
	return tree;
}

static void to_rpn(const Proof* pr, vector<Node>& proof) {
	for (auto& node : pr->refs) {
		switch(node.type) {
		case Node::ESSENTIAL:
		case Node::FLOATING:
		case Node::AXIOM:
		case Node::THEOREM:
			proof.push_back(node);
			break;
		case Node::PROOF:
			to_rpn(node.val.prf, proof);
			break;
		default : assert(false && "impossible"); break;
		}
	}
}

Proof* to_rpn(const Proof* pr) {
	Proof* rpn = new Proof();
	vector<Node>& proof = rpn->refs;
	to_rpn(pr, proof);
	return rpn;
}

void transform(Proof* proof, const Transform& trans, bool forward) {
	assert(proof->tree);
	for (uint i = 0; i < proof->refs.size() - 1; ++ i) {
		if (proof->refs[i].type == Node::PROOF)
			transform(proof->refs[i].val.prf, trans);
	}
	Node op = proof->refs.back();
	assert(op.type == Node::AXIOM || op.type == Node::THEOREM);
	Perm perm = trans.find(ass_label(op))->second;
	assert(perm.size() + 1 == proof->refs.size());
	vector<Node> new_refs = proof->refs;
	for (uint i = 0; i < new_refs.size() - 1; ++ i)
		if (forward) new_refs[perm[i]] = proof->refs[i];
		else         new_refs[i] = proof->refs[perm[i]];
	proof->refs = new_refs;
}

}} // mdl::mm



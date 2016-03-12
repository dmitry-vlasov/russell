#include <boost/range/adaptor/reversed.hpp>

#include "mm/ast.hpp"
#include "tree.hpp"

namespace mdl { namespace mm {

inline uint arity(const Node& node) {
	return node.type == Node::AXIOM ? node.val.ax->arity : node.val.th->arity;
}

Proof* to_tree(const Proof* proof) {
	stack<Node> stack;
	for (auto n : proof->refs) {
		switch(n.type) {
		case Node::ESSENTIAL:
		case Node::FLOATING:
		case Node::PROOF:
			// Operand
			stack.push(n);
			break;
		case Node::AXIOM:
		case Node::THEOREM: {
			// Operator
			Proof* p = new Proof();
			p->tree = true;
			p->refs.push_back(n);
			for (uint i = 0; i < n.val.ax->arity; ++ i) {
				p->refs.push_back(stack.top());
				stack.pop();
			}
			std::reverse(p->refs.begin(), p->refs.end());
			stack.push(p);
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

inline uint ass_label(const Node& node) {
	return node.type == Node::AXIOM ? node.val.ax->label : node.val.th->label;
}

void transform(Proof* proof, Transform& trans) {
	assert(proof->tree);
	for (uint i = 0; i < proof->refs.size() - 1; ++ i) {
		if (proof->refs[i].type == Node::PROOF)
			transform(proof->refs[i].val.prf, trans);
	}
	Node op = proof->refs.back();
	assert(op.type == Node::AXIOM || op.type == Node::THEOREM);
	Perm perm = trans[ass_label(op)];
	vector<Node> new_refs = proof->refs;
	for (uint i = 0; i < new_refs.size() - 1; ++ i)
		new_refs[i] = proof->refs[perm[i]];
	proof->refs = new_refs;
}

}} // mdl::mm



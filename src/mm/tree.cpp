//#include <boost/range/adaptor/reversed.hpp>

#include "mm/ast.hpp"
#include "mm/tree.hpp"
#include "mm/globals.hpp"

namespace mdl { namespace mm {

Proof* to_tree(const Proof* proof) {
	stack<Ref> stack;
	for (auto r : proof->refs) {
		switch(r.type) {
		case Ref::ESSENTIAL:
		case Ref::FLOATING:
			stack.push(r);
			break;
		case Ref::AXIOM:
		case Ref::THEOREM: {
			Proof* p = new Proof(true);
			p->refs.push_back(r);
			for (uint i = 0; i < r.arity(); ++ i) {
				p->refs.push_back(stack.top());
				stack.pop();
			}
			std::reverse(p->refs.begin(), p->refs.end());
			stack.push(Ref(p));
		}	break;
		default : assert(false && "impossible"); break;
		}
	}
	Proof* tree =
		 stack.top().type == Ref::PROOF ?
		 stack.top().val.prf :
		 nullptr;
	stack.pop();
	assert(stack.empty());
	return tree;
}

static void to_rpn(const Proof* pr, vector<Ref>& proof) {
	for (auto& node : pr->refs) {
		switch(node.type) {
		case Ref::ESSENTIAL:
		case Ref::FLOATING:
		case Ref::AXIOM:
		case Ref::THEOREM:
			proof.push_back(node);
			break;
		case Ref::PROOF:
			to_rpn(node.val.prf, proof);
			break;
		default : assert(false && "impossible"); break;
		}
	}
}

Proof* to_rpn(const Proof* pr) {
	Proof* rpn = new Proof();
	vector<Ref>& proof = rpn->refs;
	to_rpn(pr, proof);
	return rpn;
}

void transform(Proof* proof, const Transform& trans, bool forward) {
	assert(proof->tree);
	for (uint i = 0; i < proof->refs.size() - 1; ++ i) {
		if (proof->refs[i].type == Ref::PROOF)
			transform(proof->refs[i].val.prf, trans);
	}
	Ref op = proof->refs.back();
	assert(op.type == Ref::AXIOM || op.type == Ref::THEOREM);
	Perm perm = trans.find(op.label())->second;
	assert(perm.size() + 1 == proof->refs.size());
	vector<Ref> new_refs = proof->refs;
	for (uint i = 0; i < new_refs.size() - 1; ++ i)
		if (forward) new_refs[perm[i]] = proof->refs[i];
		else         new_refs[i] = proof->refs[perm[i]];
	proof->refs = new_refs;
}

void reduce_ref(Ref& ref, const set<uint>& red) {
	if (ref.type == Ref::PROOF) {
		Proof* proof = ref.val.prf;
		if (red.find(proof->refs.back().label()) != red.end()) {
			ref = proof->refs[proof->refs.size() - 2];
			proof->refs[proof->refs.size() - 2].type = Ref::NONE;
			delete proof;
			reduce_ref(ref, red);
		} else {
			for (Ref& r : proof->refs)
				reduce_ref(r, red);
		}
	}
}

void reduce(Proof*& proof, const set<uint>& red) {
	Ref ref = Ref(proof);
	reduce_ref(ref, red);
	assert(ref.type == Ref::PROOF);
	proof = ref.val.prf;
}

}} // mdl::mm



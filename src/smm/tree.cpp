#include "smm/ast.hpp"
#include "smm/tree.hpp"

namespace mdl { namespace smm {

Proof* to_tree(const Proof* proof) {
	stack<Ref*> stack;
	for (auto r : proof->refs) {
		switch(r->type) {
		case Ref::ESSENTIAL:
		case Ref::FLOATING:
		case Ref::INNER:
			stack.push(r); break;
		case Ref::AXIOM:
		case Ref::THEOREM: {
			Proof* tree = new Proof(Proof::TREE);
			tree->refs.push_back(r);
			for (uint i = 0; i < r->val.ass->arity(); ++ i) {
				tree->refs.push_back(stack.top());
				stack.pop();
			}
			std::reverse(tree->refs.begin(), tree->refs.end());
			stack.push(new Ref(tree));
		}	break;
		default : assert(false && "impossible"); break;
		}
	}
	Proof* tree = stack.top()->val.prf;
	stack.pop();
	assert(stack.empty());
	return tree;
}

static void to_rpn(const Proof* tree, vector<Ref*>& proof) {
	for (auto r : tree->refs) {
		if (r->type == Ref::PROOF)
			to_rpn(r->val.prf, proof);
		else
			proof.push_back(r);
	}
}

Proof* to_rpn(const Proof* tree) {
	Proof* rpn = new Proof();
	vector<Ref*>& proof = rpn->refs;
	to_rpn(tree, proof);
	return rpn;
}

void transform(Proof* tree, const Transform& trans, bool forward) {
	for (uint i = 0; i + 1 < tree->refs.size(); ++ i) {
		if (tree->refs[i]->type == Ref::PROOF)
			transform(tree->refs[i]->val.prf, trans);
	}
	Ref* op = tree->refs.back();
	Perm perm = trans.find(op->label())->second;
	assert(perm.size() + 1 == tree->refs.size());
	vector<Ref*> new_refs = tree->refs;
	for (uint i = 0; i < new_refs.size() - 1; ++ i)
		if (forward) new_refs[perm[i]] = tree->refs[i];
		else         new_refs[i] = tree->refs[perm[i]];
	tree->refs = new_refs;
}

Vect eval(Proof* proof);

Vect eval(Ref* ref) {
	if (ref->expr.size()) return ref->expr;
	switch (ref->type) {
	case Ref::ESSENTIAL: ref->expr = ref->val.ess->expr; break;
	case Ref::FLOATING:  ref->expr = ref->val.flo->expr; break;
	case Ref::INNER:	 ref->expr = ref->val.inn->expr; break;
	case Ref::PROOF:     ref->expr = eval(ref->val.prf); break;
	default : assert(false && "impossible"); break;
	}
	return ref->expr;
}

Vect eval(Proof* proof) {
	assert(proof->type == Proof::TREE);
	Ref* ref = proof->refs.back();
	if (ref->expr.size())
		return ref->expr;

	const Assertion* ass = ref->val.ass;
	Subst sub;
	uint flo_ind = 0, esss = ass->essential.size();
	for (auto flo : ass->floating) {
		sub[flo->var()] = eval(proof->refs[esss + flo_ind ++]);
	}
	uint ess_ind = 0;
	for (auto ess : ass->essential) {
		if (apply(sub, ess->expr) != eval(proof->refs[ess_ind ++])) {
			string msg = "hypothesis mismatch:\n";
			msg += show_ex(apply(sub, ess->expr)) + "\n";
			msg += "and\n";
			msg += show_ex(eval(proof->refs[ess_ind])) + "\n";
			msg += "assertion " + Sys::get().lex.labels.toStr(ass->prop->label) + "\n";
			throw Error("verification", msg);
		}
	}
	ref->expr = apply(sub, ass->prop->expr);
	return ref->expr;
}

}} // mdl::mm



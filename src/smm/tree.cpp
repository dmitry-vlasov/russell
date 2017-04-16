#include "smm/ast.hpp"
#include "smm/tree.hpp"

namespace mdl { namespace smm {

typedef map<uint, uint> Perm;
typedef map<uint, Perm> Transform;
typedef map<Symbol, Vect> Subst;


Tree* to_tree(const Proof* proof) {
	stack<Tree*> stack;
	for (Ref* r : proof->refs) {
		switch(r->type) {
		case Ref::ESSENTIAL:
		case Ref::FLOATING:
		case Ref::INNER:
			stack.push(new Tree(r));
			break;
		case Ref::AXIOM:
		case Ref::THEOREM: {
			Tree* t = new Tree();
			t->nodes.push_back(r);
			for (uint i = 0; i < r->val.ass->arity(); ++ i) {
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
	if (op->type == Ref::AXIOM || op->type == Ref::THEOREM) {
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

Vect eval(Tree* proof);

Vect eval(Tree::Node& n) {
	if (!n.expr.size()) {
		switch (n.type) {
		case Tree::Node::TREE: n.expr = eval(n.val.tree); break;
		case Tree::Node::REF: {
			Ref* ref = n.val.ref;
			switch (ref->type) {
			case Ref::ESSENTIAL: n.expr = ref->val.ess->expr; break;
			case Ref::FLOATING:  n.expr = ref->val.flo->expr; break;
			case Ref::INNER:	 n.expr = ref->val.inn->expr; break;
			default : assert(false && "impossible");
			}
		}}
	}
	return n.expr;
}

Vect eval(Tree* tree) {
	Tree::Node& n = tree->nodes.back();
	if (n.expr.size()) return n.expr;
	assert(n.type == Tree::Node::REF);
	Ref* ref = n.val.ref;
	if (ref->type != Ref::THEOREM && ref->type != Ref::AXIOM) return eval(n);
	const Assertion* ass = ref->val.ass;
	Subst sub;
	uint flo_ind = 0, esss = ass->essential.size();
	for (auto flo : ass->floating) {
		Tree::Node& f = tree->nodes[esss + flo_ind ++];
		sub[flo->var()] = eval(f);
	}
	uint ess_ind = 0;
	for (auto ess : ass->essential) {
		if (apply(sub, ess->expr) != eval(tree->nodes[ess_ind ++])) {
			string msg = "hypothesis mismatch:\n";
			msg += show_ex(apply(sub, ess->expr)) + "\n";
			msg += "and\n";
			msg += show_ex(eval(tree->nodes[ess_ind])) + "\n";
			msg += "assertion " + Lex::toStr(ass->prop.label) + "\n";
			throw Error("verification", msg);
		}
	}
	n.expr = apply(sub, ass->prop.expr);
	return n.expr;
}


/*
Proof* to_tree(const Proof* proof) {
	stack<Ref*> stack;
	for (auto r : proof->refs) {
		switch(r->type) {
		case Ref::ESSENTIAL:
		case Ref::FLOATING:
		case Ref::INNER:
			stack.push(new Ref(*r)); break;
		case Ref::AXIOM:
		case Ref::THEOREM: {
			Proof* tree = new Proof(Proof::TREE);
			tree->refs.push_back(new Ref(*r));
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
	stack.top()->val.prf = nullptr;
	delete stack.top();
	stack.pop();
	assert(stack.empty());
	return tree;
}

static void to_rpn(const Proof* tree, vector<Ref*>& proof) {
	for (auto r : tree->refs) {
		if (r->type == Ref::PROOF)
			to_rpn(r->val.prf, proof);
		else
			proof.push_back(new Ref(*r));
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
	for (uint i = 0; i < new_refs.size() - 1; ++ i) {
		Ref* r = forward ? tree->refs[i] : tree->refs[perm[i]];
		if (forward) new_refs[perm[i]] = new Ref(*r);
		else         new_refs[i] = new Ref(*r);
		delete r;
	}
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
			msg += "assertion " + Lex::toStr(ass->prop.label) + "\n";
			throw Error("verification", msg);
		}
	}
	ref->expr = apply(sub, ass->prop.expr);
	return ref->expr;
}
*/
}} // mdl::mm



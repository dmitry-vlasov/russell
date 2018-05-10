#include <mm2_ast.hpp>
#include "mm2_tree.hpp"

namespace mdl { namespace mm2 {

typedef map<uint, uint> Perm;
typedef map<uint, Perm> Transform;
typedef map<Symbol, Expr> Subst;

inline void append_expr(Expr& ex_1, const Expr& ex_2) {
	auto it = ex_2.cbegin();
	++ it;
	for (; it != ex_2.cend(); ++ it)
		ex_1.push_back(*it);
}

Expr apply_subst(const Subst& sub, const Expr& expr) {
	Expr ret;
	for (auto s : expr) {
		if (s.var) {
			auto ex = sub.find(s);
			if (ex == sub.cend())
				ret.push_back(s);
			else
				append_expr(ret, ex->second);
		} else
			ret.push_back(s);
	}
	return  ret;
}

Tree* to_tree(const Proof* proof) {
	stack<Tree*> stack;
	for (const Ref& r : proof->refs) {
		if (r.is_assertion()) {
			Tree* t = new Tree();
			t->nodes.push_back(&r);
			for (uint i = 0; i < r.ass()->arity(); ++ i) {
				t->nodes.push_back(stack.top());
				stack.pop();
			}
			std::reverse(t->nodes.begin(), t->nodes.end());
			stack.push(t);
		} else {
			stack.push(new Tree(&r));
		}
	}
	Tree* tree = stack.top();
	stack.pop();
	if (!stack.empty())
		throw Error("non-empty stack at the end of the proof");
	return tree;
}

static void to_proof(const Tree* t, vector<Ref>& proof) {
	for (auto n : t->nodes) {
		switch(n.type) {
		case Tree::Node::REF:
			proof.emplace_back(*n.val.ref);
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

void transform(Tree* tree, bool forward) {
	for (uint i = 0; i < tree->nodes.size() - 1; ++ i) {
		if (tree->nodes[i].type == Tree::Node::TREE)
			transform(tree->nodes[i].val.tree, forward);
	}
	assert(tree->nodes.back().type == Tree::Node::REF);
	const Ref* op = tree->nodes.back().val.ref;
	if (op->is_assertion()) {
		Perm perm = compute_permutation(op->ass());
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
			const Ref* ref = n.val.ref;
			switch (ref->val.index()) {
			case 0 /* Var */ : n.expr = ref->var()->expr; break;
			case 1 /* Hyp */ : n.expr = ref->hyp()->expr; break;
			case 2 /* Ass */ : n.expr = ref->ass()->expr; break;
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
	const Ref* ref = n.val.ref;
	if (!ref->is_assertion()) return eval(n);
	const Assertion* ass = ref->ass();
	Subst sub;
	uint flo_ind = 0, esss = ass->hyps.size();
	for (const auto& flo : ass->outerVars) {
		Tree::Node& f = tree->nodes[esss + flo_ind ++];
		sub[flo.get()->var()] = eval(f);
	}
	uint ess_ind = 0;
	for (const auto& ess : ass->hyps) {
		if (apply_subst(sub, ess.get()->expr) != eval(tree->nodes[ess_ind ++])) {
			string msg = "hypothesis mismatch:\n";
			msg += show_ex(apply_subst(sub, ess.get()->expr)) + "\n";
			msg += "and\n";
			msg += show_ex(eval(tree->nodes[ess_ind])) + "\n";
			msg += "assertion " + Lex::toStr(ass->id()) + "\n";
			throw Error("verification", msg);
		}
	}
	n.expr = apply_subst(sub, ass->expr);
	return n.expr;
}

}} // mdl::smm



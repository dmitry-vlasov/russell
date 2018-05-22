#include "mm_tree.hpp"
#include "mm_ast.hpp"

namespace mdl { namespace mm {

inline void append_expr(Expr& ex_1, const Expr& ex_2) {
	auto it = ex_2.cbegin();
	++ it;
	for (; it != ex_2.cend(); ++ it)
		ex_1.push_back(*it);
}

string Tree::Node::show() const {
	if (kind() == Tree::Node::TREE) return tree()->show();
	ostringstream oss;
	switch (ref()->kind()) {
	case Ref::VAR : ref()->var()->ref(oss); break;
	case Ref::HYP : ref()->hyp()->ref(oss); break;
	case Ref::ASS : ref()->ass()->ref(oss); break;
	}
	if (expr.size()) {
		oss << "[[" << expr << "]]";
	}
	return oss.str();
}

string Tree::show() const {
	string space = length() > 16 ? "\n" : " ";
	assert(nodes.back().kind() == Tree::Node::REF);
	const Node& n = nodes.back();
	string str = n.show();
	str += "(";
	for (uint i = 0; i + 1 < nodes.size(); ++ i)
		str += Indent::paragraph(space + nodes[i].show(), "  ");
	str += space + ") ";
	return str;
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
	for (auto& n : t->nodes) {
		switch(n.kind()) {
		case Tree::Node::REF:
			proof.emplace_back(*n.ref());
			break;
		case Tree::Node::TREE:
			to_proof(n.tree(), proof);
			break;
		default : assert(false && "impossible"); break;
		}
	}
}

Tree* reduce(Tree* tree, const map<uint, Ref*>& red) {
	assert(tree->nodes.back().type == Tree::Node::REF);
	uint l = tree->nodes.back().ref()->label();
	if (red.count(l)) {
		Ref* ref = red.at(l);
		Tree* t = nullptr;
		if (ref->is_assertion()) {
			t = new Tree(ref);
		} else {
			const uint arg = tree->nodes.size() - 2;
			assert(tree->nodes[arg].type == Tree::Node::TREE);
			t = tree->nodes[arg].tree();
			tree->nodes[arg].set(nullptr);
		}
		return reduce(t, red);
	} else {
		for (auto& n : tree->nodes) {
			if (n.kind() == Tree::Node::TREE) {
				Tree* reduced = reduce(n.tree(), red);
				if (reduced != n.tree()) {
					n.set(reduced);
				}
			}
		}
		return tree;
	}
}

Proof* to_proof(const Tree* tree) {
	Proof* proof = new Proof();
	to_proof(tree, proof->refs);
	return proof;
}

Expr eval(Tree* proof);

Expr eval(Tree::Node& n) {
	if (!n.expr.size()) {
		switch (n.kind()) {
		case Tree::Node::TREE: n.expr = eval(n.tree()); break;
		case Tree::Node::REF: {
			const Ref* ref = n.ref();
			switch (ref->kind()) {
			case Ref::VAR : n.expr = ref->var()->expr; break;
			case Ref::HYP : n.expr = ref->hyp()->expr; break;
			case Ref::ASS : n.expr = ref->ass()->expr; break;
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
	const Ref* ref = n.ref();
	if (!ref->is_assertion()) return eval(n);
	const Assertion* ass = ref->ass();
	Subst sub;
	uint ind = 0;
	for (const auto& flo : ass->outerVars) {
		Tree::Node& f = tree->nodes[ind ++];
		sub[flo.get()->var()] = eval(f);
	}
	for (const auto& ess : ass->hyps) {
		Expr from_ass = apply_subst(sub, ess.get()->expr);
		Expr from_proof = eval(tree->nodes[ind ++]);
		if (from_ass != from_proof) {
			string msg = "hypothesis mismatch:\n";
			msg += "hyp from assertion: " + show_ex(from_ass) + "\n";
			msg += "and\n";
			msg += "hyp from proof: " + show_ex(from_proof) + "\n";
			msg += "assertion " + Lex::toStr(ass->id()) + "\n";
			msg += show(*ass) + "\n";
			msg += "substitution:\n"  + show(sub) + "\n";
			msg += "tree: " + tree->show() + "\n";
			throw Error("verification", msg);
		}
	}
	n.expr = apply_subst(sub, ass->expr);
	return n.expr;
}

}} // mdl::smm

#pragma once

#include <mm2_ast.hpp>

namespace mdl { namespace mm2 {

typedef map<uint, uint> Perm;
typedef map<uint, Perm> Transform;
typedef map<Symbol, Expr> Subst;

inline string show (const Subst& subst) {
	string str;
	for (auto it : subst)
		str += show_sy(it.first) + " = > " + show_ex(it.second) + "\n";
	return str;
}
Expr apply_subst(const Subst& sub, const Expr& expr);

inline Perm create_permutation(uint flos, uint esss) {
	Perm perm;
	for (uint i = 0; i < esss; ++ i) {
		perm[i] = i + flos;
	}
	for (uint i = 0; i < flos; ++ i) {
		perm[i + esss] = i;
	}
	return perm;
}

inline Perm compute_permutation(const Assertion* ass) {
	return create_permutation(ass->outerVars.size(), ass->hyps.size());
}

struct Tree {
	struct Node {
		enum Type {
			REF,
			TREE
		};
		union Value {
			Value(const Ref* r) : ref(r) { }
			Value(Tree* t) : tree(t) { }
			Value(const Value& v) : ref(v.ref) { }
			const Ref* ref;
			Tree* tree;
		};
		Node(const Ref* r) : type(REF), val(r) { }
		Node(Tree* t) : type(TREE), val(t) { }
		void destroy() { if (type == TREE) delete val.tree; }
		uint length() const {
			return (type == Tree::Node::TREE) ? val.tree->length() : 1;
		}
		string show() const {
			if (type == Tree::Node::TREE) return val.tree->show();
			ostringstream oss;
			switch (val.ref->val.index()) {
			case 0 : val.ref->var()->ref(oss); break;
			case 1 : val.ref->hyp()->ref(oss); break;
			case 2 : val.ref->ass()->ref(oss); break;
			}
			return oss.str();
		}
		Type type;
		Value val;
		Expr expr;
	};
	Tree() = default;
	Tree(const Ref* r) { nodes.push_back(r); }
	~Tree() { for (auto& n : nodes) n.destroy(); }
	uint length() const {
		uint len = 0;
		for (auto& n : nodes) len += n.length();
		return len;
	}
	string show() const {
		string space = length() > 16 ? "\n" : " ";
		assert(nodes.back().type == Tree::Node::REF);
		const Node& n = nodes.back();
		string str = n.show();
		str += "(";
		for (uint i = 0; i + 1 < nodes.size(); ++ i)
			str += Indent::paragraph(space + nodes[i].show(), "  ");
		str += space + ") ";
		return str;
	}
	vector<Node> nodes;
};

Tree* to_tree(const Proof*);
Proof* to_proof(const Tree*);
void transform(Tree*, bool forward = true);
Expr eval(Tree* proof);
Expr eval(Ref*);

}} // mdl::smm

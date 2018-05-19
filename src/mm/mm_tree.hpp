#pragma once

#include "mm_ast.hpp"

namespace mdl { namespace mm {

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
			if (expr.size()) {
				oss << "[[" << expr << "]]";
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
Tree* reduce(Tree* tree, const map<uint, Ref*>& red);
Expr eval(Tree* proof);
Expr eval(Ref*);

}} // mdl::smm

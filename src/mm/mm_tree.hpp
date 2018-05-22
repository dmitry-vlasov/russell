#pragma once

#include "mm_ast.hpp"

namespace mdl { namespace mm {

struct Tree {
	struct Node {
		enum Kind { REF, TREE };
		typedef variant<const Ref*, unique_ptr<Tree>> Value;

		Node(const Ref* r) : val(r) { }
		Node(Tree* t) : val(unique_ptr<Tree>(t)) { }
		uint length() const {
			return (kind() == Tree::Node::TREE) ? tree()->length() : 1;
		}
		Kind kind() const { return static_cast<Kind>(val.index()); }
		string show() const;
		const Ref* ref() const { return std::get<const Ref*>(val); }
		Tree* tree() const { return std::get<unique_ptr<Tree>>(val).get(); }
		void set(Tree* tree) { val = unique_ptr<Tree>(tree); }
		Value val;
		Expr expr;
	};
	Tree() = default;
	Tree(const Ref* r) { nodes.push_back(r); }

	uint length() const {
		uint len = 0;
		for (auto& n : nodes) len += n.length();
		return len;
	}
	string show() const;
	vector<Node> nodes;
};

Tree* to_tree(const Proof*);
Proof* to_proof(const Tree*);
void transform(Tree*, bool forward = true);
Tree* reduce(Tree* tree, const map<uint, Ref*>& red);
Expr eval(Tree* proof);
Expr eval(Ref*);

}} // mdl::smm

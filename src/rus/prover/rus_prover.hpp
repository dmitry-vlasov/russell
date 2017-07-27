#pragma once

#include "rus_ast.hpp"

namespace mdl { namespace rus { namespace prover {

class Proof;

struct Node {
	enum Kind { PROP, HYP, ROOT, REF };
	Node*          parent;
	vector<Node*>  child;
	vector<Proof*> proof;
	virtual Kind kind() const = 0;
	virtual ~Node();
};

struct Prop : public Node {
	const Assertion* ass;
	Substitution*    sub;
	Kind kind() const { return PROP; }
	~Prop() override { delete sub; }
};

struct Hyp : public Node {
	Expr expr;
	Kind kind() const { return HYP; }
	~Hyp() override { }
};

struct Root : public Hyp {
	Kind kind() const { return ROOT; }
	~Root() override { }
};

struct Ref : public Node {
	Node* node;
	Substitution* sub;
	Kind kind() const { return REF; }
	~Ref() override { delete sub; }
};

struct Proof {
	Node*          node;
	Proof*         parent;
	vector<Proof*> child;
	Substitution*  sub;
	bool           newOne;
	~Proof() {
		delete sub;
		for (auto n : child) delete n;
	}
};

inline Node::~Node()  {
	for (auto n : child) delete n;
	for (auto p : proof) delete p;
}

vector<Node*> build_up(Node*, const Assertion* = nullptr);
void build_down(vector<Node*>);

}}}


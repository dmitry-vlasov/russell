#pragma once

#include "rus_ast.hpp"

namespace mdl { namespace rus { namespace prover {

class Space;
class Proof;
class Prop;
class Hyp;
class Ref;

struct Node {
	enum Kind { PROP, HYP, REF };
	Node*          parent;
	vector<Node*>  child;
	vector<Proof*> proof;
	Space*         space;
	Node(Space* s) : parent(nullptr), space(s) { }
	Node(Node* p) : parent(p), space(p->space) {
		if (p) p->child.push_back(this);
	}
	virtual Kind kind() const = 0;
	virtual ~Node();
};

Prop* prop(Node* n);
Hyp*  hyp (Node* n);
Ref*  ref (Node* n);

struct PropRef {
	User<Assertion> ass;
	uint prop;
};

inline bool operator < (const PropRef& a1, const PropRef& a2) {
	return a1.ass == a2.ass ? a1.prop  < a2.prop : a1.ass < a2.ass;
}

struct Prop : public Node {
	PropRef      prop;
	Substitution sub;
	Prop(PropRef r, const Substitution& s, Node* p) :
		Node(p), prop(r), sub(s) { }
	Kind kind() const { return PROP; }
};

struct Hyp : public Node {
	Expr expr;
	Hyp(const Expr& e, Space* s) :
		Node(s), expr(e) { }
	Hyp(const Expr& e, Node* p) :
		Node(p), expr(p ? apply(prop(p)->sub, e) : e) { }
	Kind kind() const { return HYP; }
};

struct Ref : public Node {
	Node* node;
	Substitution sub;
	Ref(Node* n, const Substitution& s, Node* p) :
		Node(p), node(n), sub(s) { }
	Kind kind() const { return REF; }
};

struct Proof {
	Node*          node;
	Proof*         parent;
	vector<Proof*> child;
	bool           new_;
	Substitution   sub;
	~Proof() { for (auto n : child) delete n; }
};

inline Node::~Node()  {
	for (auto n : child) delete n;
	for (auto p : proof) delete p;
}

inline Prop* prop(Node* n) { return dynamic_cast<Prop*>(n); }
inline Hyp*  hyp (Node* n) { return dynamic_cast<Hyp*>(n); }
inline Ref*  ref (Node* n) { return dynamic_cast<Ref*>(n); }

vector<Node*> build_up(Node*);
vector<Node*> build_down(Node*);

}}}


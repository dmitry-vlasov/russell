#pragma once

#include "rus_ast.hpp"

namespace mdl { namespace rus { namespace prover {

class Proof;
class Prop;
class Hyp;
class Ref;

struct Node {
	enum Kind { PROP, HYP, REF };
	Node*          parent;
	vector<Node*>  child;
	vector<Proof*> proof;
	Node(Node* p) : parent(p) { if (p) p->child.push_back(this); }
	virtual Kind kind() const = 0;
	virtual ~Node();
};

Prop* prop(Node* n);
Hyp*  hyp (Node* n);
Ref*  ref (Node* n);

struct Prop : public Node {
	Assertion*    ass;
	Substitution* sub;
	Prop(Assertion* a, Substitution* s, Node* p) :
		Node(p), ass(a), sub(s) { }
	Kind kind() const { return PROP; }
	~Prop() override { delete sub; }
};

struct Hyp : public Node {
	Expr expr;
	Hyp(const Expr& e, Node* p = nullptr) :
		Node(p), expr(p ? apply(prop(p)->sub, e) : e) { }
	Kind kind() const { return HYP; }
	~Hyp() override { }
};

struct Ref : public Node {
	Node* node;
	Substitution* sub;
	Ref(Node* n, Substitution* s, Node* p) :
		Node(p), node(n), sub(s) { }
	Kind kind() const { return REF; }
	~Ref() override { delete sub; }
};

struct Proof {
	Node*          node;
	Proof*         parent;
	vector<Proof*> child;
	Substitution*  sub;
	bool           new_;
	~Proof() {
		delete sub;
		for (auto n : child) delete n;
	}
};

inline Node::~Node()  {
	for (auto n : child) delete n;
	for (auto p : proof) delete p;
}

inline Prop* prop(Node* n) { return dynamic_cast<Prop*>(n); }
inline Hyp*  hyp (Node* n) { return dynamic_cast<Hyp*>(n); }
inline Ref*  ref (Node* n) { return dynamic_cast<Ref*>(n); }

template<class D>
struct Unified {
	typedef D Data;
	Data*         data;
	Substitution* sub;
};

template<class D>
struct Index {
	virtual vector<Unified<D>> unify(const Expr& e) const = 0;
};


vector<Node*> build_up(Node*);
void build_down(vector<Node*>);

}}}


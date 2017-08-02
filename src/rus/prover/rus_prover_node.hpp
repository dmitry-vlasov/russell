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
	virtual vector<Node*> buildUp() = 0;
	virtual vector<Node*> buildDown() = 0;
	virtual ~Node();
};

Prop* prop(Node* n);
Hyp*  hyp (Node* n);
Ref*  ref (Node* n);

struct PropRef {
	User<Assertion> ass;
	uint prop;
};

struct HypRef {
	User<Assertion> ass;
	uint hyp;
};

inline bool operator < (const PropRef& a1, const PropRef& a2) {
	return a1.ass == a2.ass ? a1.prop  < a2.prop : a1.ass < a2.ass;
}

struct Prop : public Node {
	PropRef      prop;
	Substitution sub;
	Prop(PropRef r, const Substitution& s, Node* p);
	Kind kind() const override { return PROP; }
	vector<Node*> buildUp() override;
	vector<Node*> buildDown() override;
};

struct Hyp : public Node {
	Expr expr;
	Hyp(const Expr& e, Space* s) :
		Node(s), expr(e) { addToLeafs(); }
	Hyp(const Expr& e, Node* p) :
		Node(p), expr(p ? apply(prop(p)->sub, e) : e) { addToLeafs(); }
	Kind kind() const override{ return HYP; }
	vector<Node*> buildUp() override;
	vector<Node*> buildDown() override;

private:
	void addToLeafs();
};

struct Ref : public Node {
	Node* node;
	Substitution sub;
	Ref(Node* n, const Substitution& s, Node* p) :
		Node(p), node(n), sub(s) { }
	Kind kind() const override { return REF; }
	vector<Node*> buildUp() override;
	vector<Node*> buildDown() override;
};

struct Proof {
	Substitution sub;
	Expr         expr;
	Proof*       parent;
	bool         new_;
	Proof(const Substitution& s = Substitution()) :
		sub(s), parent(nullptr), new_(true) { }
	virtual ~Proof() { }
};

struct ProofHyp : public Proof {
	HypRef hyp;
};

struct ProofStep : public Proof {
	Node*          node;
	vector<Proof*> child;
	ProofStep(Node* n, vector<Proof*>&& c, const Substitution& s = Substitution()) :
		Proof(s), node(n), child(std::move(c)) { }
	~ProofStep() override { for (auto n : child) delete n; }
};

inline Prop* prop(Node* n) { return dynamic_cast<Prop*>(n); }
inline Hyp*  hyp (Node* n) { return dynamic_cast<Hyp*>(n); }
inline Ref*  ref (Node* n) { return dynamic_cast<Ref*>(n); }

}}}


#pragma once

#include "rus_ast.hpp"

namespace mdl { namespace rus { namespace prover {

struct PropRef {
	PropRef(const Assertion* a, uint i) : ass(a->id()), ind(i) { }
	Assertion* assertion() { return ass.get(); }
	const Assertion* assertion() const { return ass.get(); }
	uint id() const { return ass.id(); }
	rus::Prop* get() { return ass.get()->props[ind]; }
	friend bool operator < (const PropRef& a1, const PropRef& a2) {
		return a1.ass == a2.ass ? a1.ind  < a2.ind : a1.ass < a2.ass;
	}
private:
	User<Assertion> ass;
	uint ind;
};

struct HypRef {
	HypRef(const Assertion* a, uint i) : ass(a->id()), ind(i) { }
	Assertion* assertion() { return ass.get(); }
	rus::Hyp* get() { return ass.get()->hyps[ind]; }
	friend bool operator < (const HypRef& a1, const HypRef& a2) {
		return a1.ass == a2.ass ? a1.ind  < a2.ind : a1.ass < a2.ass;
	}
private:
	User<Assertion> ass;
	uint ind;
};

class Space;
class ProofElem;
class Prop;
class Hyp;
class Ref;

struct Node {
	enum Kind { PROP, HYP, REF };
	Node*          parent;
	vector<Node*>  child;
	vector<ProofElem*> proof;
	Space*         space;
	Node(Space* s) : parent(nullptr), space(s) { }
	Node(Node* p);
	virtual Kind kind() const = 0;
	virtual vector<Node*> buildUp() = 0;
	virtual vector<Node*> buildDown() = 0;
	virtual const Expr* expr() const = 0;
	virtual const PropRef* prop() const = 0;
	virtual ~Node();
};

Prop* prop(Node* n);
Hyp*  hyp (Node* n);
Ref*  ref (Node* n);


struct Prop : public Node {
	PropRef      prop_;
	Substitution sub_;
	Prop(const PropRef& r, const Substitution& s, Node* p);
	Kind kind() const override { return PROP; }
	vector<Node*> buildUp() override;
	vector<Node*> buildDown() override;
	const Expr* expr() const override { return parent->expr(); }
	const PropRef* prop() const override { return &prop_; }
};

struct Hyp : public Node {
	Expr expr_;
	Hyp(const Expr& e, Space* s) :
		Node(s), expr_(e) { complete(); }
	Hyp(const Expr& e, Node* p) :
		Node(p), expr_(p ? apply(prover::prop(p)->sub_, e) : e) { complete(); }
	Kind kind() const override{ return HYP; }
	vector<Node*> buildUp() override;
	vector<Node*> buildDown() override;
	const Expr* expr() const override { return &expr_; }
	const PropRef* prop() const override { return parent ? parent->prop() : nullptr; }

private:
	void complete();
};

struct Ref : public Node {
	Node* node_;
	Substitution sub_;
	Ref(Node* n, const Substitution& s, Node* p) :
		Node(p), node_(n), sub_(s) { }
	Kind kind() const override { return REF; }
	vector<Node*> buildUp() override;
	vector<Node*> buildDown() override;
	const Expr* expr() const override { return parent->expr(); }
	const PropRef* prop() const override { return parent->prop(); }
};

struct ProofElem {
	ProofElem(const Substitution& s) : sub_(s), new_(true) { }

	virtual ~ProofElem() { }
	virtual rus::Ref* ref() = 0;

	const Substitution& sub() { return sub_; }
	const Expr& expr() const { return expr_; }
	bool isNew() const { return new_; }
	const vector<ProofElem*>& parents() { return parents_; }
	void addParent(ProofElem* p) {
		parents_.push_back(p);
		new_ = false;
	}

protected:
	Substitution   sub_;
	Expr           expr_;
	vector<ProofElem*> parents_;
	bool           new_;
};

struct ProofHyp : public ProofElem {
	ProofHyp(const HypRef& h, const Substitution& s) :
		ProofElem(s), hyp_(h) { }
	rus::Ref* ref() override;
private:
	HypRef hyp_;
};

struct ProofStep : public ProofElem {
	ProofStep(Node* n, vector<ProofElem*>&& c, const Substitution& s = Substitution()) :
		ProofElem(s), node_(n), child_(std::move(c)) {
		for (auto ch : child_) ch->addParent(this);
	}
	~ProofStep() override { }
	rus::Step* step();
	rus::Ref* ref() override;
private:
	Node*          node_;
	vector<ProofElem*> child_;
};

rus::Proof* make_proof(rus::Step*, uint th, rus::Prop* prop);

inline Prop* prop(Node* n) { return dynamic_cast<Prop*>(n); }
inline Hyp*  hyp (Node* n) { return dynamic_cast<Hyp*>(n); }
inline Ref*  ref (Node* n) { return dynamic_cast<Ref*>(n); }

}}}


#pragma once

#include "rus_ast.hpp"
#include "rus_prover_expr.hpp"

namespace mdl { namespace rus { namespace prover {

struct PropRef {
	PropRef(Assertion* a = nullptr, uint i = 0) : ass(a), ind(i) { }
	uint id() const { return ass->id(); }
	rus::Prop* get() const { return ass->props[ind].get(); }
	friend bool operator < (const PropRef& a1, const PropRef& a2) {
		return a1.ass == a2.ass ? a1.ind  < a2.ind : a1.ass < a2.ass;
	}
	bool operator == (const PropRef& pr) const {
		return ass == pr.ass && ind == pr.ind;
	}
	bool operator != (const PropRef& pr) const {
		return !operator == (pr);
	}
	Assertion* ass;
	uint       ind;
};

struct HypRef {
	HypRef(Assertion* a = nullptr, uint i = 0) : ass(a), ind(i) { }
	uint id() const { return ass->id(); }
	rus::Hyp* get() const { return ass->hyps[ind].get(); }
	friend bool operator < (const HypRef& a1, const HypRef& a2) {
		return a1.ass == a2.ass ? a1.ind  < a2.ind : a1.ass < a2.ass;
	}
	bool operator == (const HypRef& hr) const {
		return ass == hr.ass && ind == hr.ind;
	}
	bool operator != (const HypRef& hr) const {
		return !operator == (hr);
	}
	Assertion* ass;
	uint       ind;
};

class Space;
class Prop;
class Hyp;
class ProofProp;
class ProofHyp;
class ProofNode;

struct Node {
	Node(Space* s) : space(s), ind(-1) { }
	Node(Node* n) : space(n->space), ind(-1) { }
	virtual ~Node();

	virtual vector<Node*> buildDown() = 0;
	virtual string show() const = 0;

	Space* space;
	uint   ind;
};

struct Prop : public Node {
	typedef vector<unique_ptr<Hyp>> Premises;
	typedef vector<unique_ptr<ProofProp>> Proofs;
	Hyp*     parent;
	Premises premises;
	Proofs   proofs;
	PropRef  prop;
	Subst    sub;
	Prop(const PropRef& r, const Subst& s, Hyp* p);

	void buildUp();
	vector<Node*> buildDown() override;
	string show() const override;
};

struct Hyp : public Node {
	typedef vector<unique_ptr<Prop>> Variants;
	typedef vector<unique_ptr<ProofHyp>> Proofs;
	Prop*     parent;
	Variants  variants;
	Proofs    proofs;
	LightTree expr;
	Hyp(const LightTree& e, Space* s);
	Hyp(const LightTree& e, Prop* p);

	void buildUp();
	vector<Node*> buildDown() override;
	string show() const override;

	void complete();
};

struct ProofNode {
	ProofNode(const Subst& s);
	virtual ~ProofNode() { }
	virtual string show() const = 0;
	virtual rus::Ref* ref() const = 0;

	Subst sub;
	bool  new_;
	uint  ind;
};

struct ProofHyp : public ProofNode {
	ProofHyp(Hyp& n, const Subst& s, const LightTree& e);
	~ProofHyp() override;

	vector<ProofProp*> parents;
	Hyp&      node;
	LightTree expr;
};

struct ProofTop : public ProofHyp {
	ProofTop(Hyp& n, const HypRef& h, const Subst& s);
	string show() const override;
	rus::Ref* ref() const override;

	HypRef hyp;
};

struct ProofExp : public ProofHyp {
	ProofExp(Hyp& h, ProofProp* c, const Subst& s = Subst());
	string show() const override;
	rus::Ref* ref() const override;
	rus::Proof* proof() const;
	ProofProp* child;
};

struct ProofProp : public ProofNode {
	ProofProp(Prop& n, const vector<ProofHyp*>& p = vector<ProofHyp*>(), const Subst& s = Subst());
	~ProofProp() override;
	rus::Ref* ref() const override;
	string show() const override;
	rus::Step* step() const;
	rus::Proof* proof() const;

	ProofHyp*         parent;
	Prop&             node;
	vector<ProofHyp*> premises;
};

string showNodeProofs(const Node* n);

}}}


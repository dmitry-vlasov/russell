#pragma once

#include "rus_ast.hpp"
#include "rus_prover_expr.hpp"

namespace mdl { namespace rus { namespace prover {

struct PropRef {
	PropRef(Assertion* a, uint i) : ass(a), ind(i) { }
	uint id() const { return ass->id(); }
	rus::Prop* get() { return ass->props[ind].get(); }
	friend bool operator < (const PropRef& a1, const PropRef& a2) {
		return a1.ass == a2.ass ? a1.ind  < a2.ind : a1.ass < a2.ass;
	}
	Assertion* ass;
	uint       ind;
};

struct HypRef {
	HypRef(Assertion* a, uint i) : ass(a), ind(i) { }
	rus::Hyp* get() { return ass->hyps[ind].get(); }
	const rus::Hyp* get() const { return ass->hyps[ind].get(); }
	friend bool operator < (const HypRef& a1, const HypRef& a2) {
		return a1.ass == a2.ass ? a1.ind  < a2.ind : a1.ass < a2.ass;
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
	Node(Space* s);
	Node(Node* n);
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
	Hyp(const LightTree& e, Space* s) : Node(s), parent(nullptr), expr(e) { complete(); }
	Hyp(const LightTree& e, Prop* p) : Node(p), parent(p), expr(p ? apply(p->sub, e) : e) { }

	void buildUp();
	vector<Node*> buildDown() override;
	string show() const override;

	void complete();
};

struct ProofNode {
	ProofNode(const Subst& s) : sub(s), new_(true) { }
	virtual ~ProofNode() { }
	virtual string show() const = 0;
	virtual rus::Ref* ref() = 0;
	Subst sub;
	bool  new_;
};

struct ProofHyp : public ProofNode {
	ProofHyp(Hyp& n, const Subst& s);
	~ProofHyp() override;

	vector<ProofProp*> parents;
	Hyp&      node;
	LightTree expr;
};

struct ProofTop : public ProofHyp {
	ProofTop(Hyp& n, const HypRef& h, const Subst& s);
	string show() const override;
	rus::Ref* ref() override;

	HypRef hyp;
};

struct ProofExp : public ProofHyp {
	ProofExp(Hyp& h, ProofProp* c, const Subst& s = Subst());
	string show() const override;
	rus::Ref* ref() override;

	ProofProp* child;
};

struct ProofProp : public ProofNode {
	ProofProp(Prop& n, const vector<ProofHyp*>& p, const Subst& s = Subst());
	~ProofProp() override;
	rus::Step* step();
	rus::Ref* ref() override;
	string show() const override;

	ProofHyp*         parent;
	Prop&             node;
	vector<ProofHyp*> premises;
};

rus::Proof* make_proof(rus::Step* step, uint theorem, rus::Prop* prop);

}}}


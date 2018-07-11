#pragma once

#include "rus_ast.hpp"

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
	virtual string show(uint mode) const = 0;

	Space* space;
	uint   ind;
};

struct Prop : public Node {
	typedef vector<unique_ptr<Hyp>> Premises;
	typedef vector<ProofProp*> Proofs;
	Hyp*         parent;
	Premises     premises;
	Proofs       proofs;
	PropRef      prop;
	Substitution sub;
	Prop(const PropRef& r, const Substitution& s, Hyp* p);

	void buildUp();
	vector<Node*> buildDown() override;
	string show(uint) const override;
};

struct Hyp : public Node {
	typedef vector<unique_ptr<Prop>> Variants;
	typedef vector<ProofHyp*> Proofs;
	Prop*    parent;
	Variants variants;
	Proofs   proofs;
	Expr     expr;
	Hyp(const Expr& e, Space* s) : Node(s), parent(nullptr), expr(e) { complete(); }
	Hyp(const Expr& e, Prop* p) : Node(p), parent(p), expr(p ? apply(p->sub, e) : e) { complete(); }

	void buildUp();
	vector<Node*> buildDown() override;
	string show(uint) const override;

private:
	void complete();
};

struct ProofNode {
	ProofNode(const Substitution& s) : sub(s), new_(true) { }
	virtual ~ProofNode() { }
	virtual string show(uint) const = 0;
	virtual rus::Ref* ref() = 0;
	Substitution sub;
	bool         new_;
};

struct ProofHyp : public ProofNode {
	ProofHyp(Hyp& n, const Substitution& s);
	rus::Ref* ref() override;

	ProofProp* parent;
	Hyp&       node;
	Expr       expr;
};

struct ProofTop : public ProofHyp {
	ProofTop(Hyp& n, const HypRef& h, const Substitution& s) : ProofHyp(n, s), hyp(h) { }
	string show(uint) const override;
	rus::Ref* ref() override;

	HypRef hyp;
};

struct ProofExp : public ProofHyp {
	ProofExp(Hyp& h, ProofProp* c, const Substitution& s = Substitution());
	string show(uint) const override;

	ProofProp* child;
};

struct ProofProp : public ProofNode {
	ProofProp(Prop& n, const vector<ProofHyp*>& p, const Substitution& s = Substitution());
	~ProofProp() override { }
	rus::Step* step();
	rus::Ref* ref() override;
	string show(uint) const override;

	ProofHyp*         parent;
	Prop&             node;
	vector<ProofHyp*> premises;
};

rus::Proof* make_proof(rus::Step*, uint th, rus::Prop* prop);

enum class ShowMode {
	THIS_IDX, CHILD_IDX, PARNT_IDX, RECURS, ASS, EXPR, SUB, PRF_SZ
};

uint   show_bits(string);
string show_bits(uint);
bool   show_bit(uint, ShowMode);

}}}


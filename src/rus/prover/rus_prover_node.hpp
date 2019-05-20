#pragma once

#include "rus_ast.hpp"
#include "rus_prover_subst.hpp"

namespace mdl { namespace rus { namespace prover {

struct PropRef {
	PropRef(Assertion* a = nullptr, uint i = 0) : ass(a), ind(i) { }
	uint id() const { return ass->id(); }
	rus::Prop* get() const { return ass->props[ind].get(); }
	friend bool operator < (const PropRef& a1, const PropRef& a2) {
		return a1.ass == a2.ass ? a1.ind  < a2.ind : a1.ass->token.preceeds(a2.ass->token);
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

	virtual bool buildDown(set<Node*>&) = 0;
	virtual string show(bool with_proofs = false) const = 0;

	Space* space;
	uint   ind;
	bool   hint = false;
};

inline std::ostream& operator << (std::ostream& os, const Node& n){
	os << n.show(); return os;
}

struct Prop : public Node {
	typedef vector<unique_ptr<Hyp>> Premises;
	typedef vector<unique_ptr<ProofProp>> Proofs;
	Hyp*     parent;
	Premises premises;
	Proofs   proofs;
	PropRef  prop;
	Subst    sub;
	Subst    outer;
	Subst    fresher;
	Prop(PropRef r, Subst&& s, Subst&& o, Subst&& f, Hyp* p);

	void buildUp();
	bool buildDown(set<Node*>&) override;
	string show(bool with_proofs = false) const override;
	bool mayGrowUp() const { return premises.size() < prop.ass->arity(); }
	bool isLeaf() const { return prop.ass->arity() == 0; }
};

struct Hyp : public Node {
	typedef vector<unique_ptr<Prop>> Variants;
	typedef vector<unique_ptr<ProofHyp>> Proofs;
	Prop*     parent;
	Variants  variants;
	Proofs    proofs;
	Term expr;
	Hyp(Term&& e, Space* s);
	Hyp(Term&& e, Prop* p);

	void buildUp();
	bool buildDown(set<Node*>&) override;
	string show(bool with_proofs = false) const override;
	bool root() const { return !parent; }

	bool unifyWithGoalHyps(const rus::Hyp* hint = nullptr);
};

struct ProofNode {
	ProofNode(const Subst& s, bool h);
	virtual ~ProofNode() { }
	virtual string show() const = 0;
	virtual rus::Ref* ref() const = 0;
	virtual bool equal(const ProofNode*) const = 0;

	Subst sub;
	bool  new_;
	uint  ind;
	bool  hint;
};

struct ProofHyp : public ProofNode {
	ProofHyp(Hyp& n, const Subst& s, const Term& e, bool h);
	~ProofHyp() override;

	vector<ProofProp*> parents;
	Hyp& node;
	Term expr;
};

struct ProofTop : public ProofHyp {
	ProofTop(Hyp& n, const HypRef& hy, const Subst& s, bool hi);
	string show() const override;
	rus::Ref* ref() const override;
	bool equal(const ProofNode* n) const override;

	HypRef hyp;
};

struct ProofExp : public ProofHyp {
	ProofExp(Hyp& hy, ProofProp* c, const Subst& s, bool hi);
	string show() const override;
	rus::Ref* ref() const override;
	bool equal(const ProofNode* n) const override;
	rus::Proof* proof() const;

	ProofProp* child;
};

struct ProofProp : public ProofNode {
	ProofProp(Prop& n, const vector<ProofHyp*>& p, const Subst& s, bool h);
	~ProofProp() override;
	rus::Ref* ref() const override;
	string show() const override;
	bool equal(const ProofNode* n) const override;
	rus::Step* step() const;
	rus::Proof* proof() const;

	ProofHyp*         parent;
	Prop&             node;
	vector<ProofHyp*> premises;
};

struct ProofHypIndexed {
	const ProofHyp* proof = nullptr;
	uint ind = -1;
	string show() const {
		string ret;
		ret += "index: " + (ind == -1 ? string("-1") : to_string(ind)) + "\n";
		ret += proof->show();
		return ret;
	}
};

string showNodeProofs(const Node* n, uint limit = -1);
bool unify_down(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& h);

// Statistics:
void add_sequential_stats(uint card, uint count, Timer& timer);
void add_matrix_stats(uint card, uint count, Timer& timer);
void add_timer_stats(const string& name, Timer& timer);
void print_statistics();

}}}


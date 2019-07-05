#pragma once

#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

struct ProofNode {
	ProofNode(const Subst& s, bool h) : sub(s), new_(true), ind(global_index()++), hint(h) { }
	ProofNode(Subst&& s, bool h) : sub(std::move(s)), new_(true), ind(global_index()++), hint(h) { }
	virtual ~ProofNode() { }
	virtual string show() const = 0;
	virtual bool equal(const ProofNode*) const = 0;
	virtual const Term& expr() const = 0;
	virtual void addParent(ProofNode*) = 0;

	Subst sub;
	bool  new_;
	uint  ind;
	bool  hint;
private:
	static uint& global_index() { static uint i = 0; return i; }
};

struct ProofExp : public ProofNode {
	ProofExp(const Subst& s, bool h) : ProofNode(s, h) { }
	ProofExp(Subst&& s, bool h) : ProofNode(std::move(s), h) { }
};

struct ProofTop : public ProofExp {
	ProofTop(Hyp& n, const HypRef& hy, const Subst& s, bool hi);
	string show() const override;
	bool equal(const ProofNode* n) const override;
	const Term& expr() const override { return expr_; }
	void addParent(ProofNode* p) override { parents.push_back(p); }

	HypRef hyp;
	Hyp& node;
	Term expr_;
	vector<ProofNode*> parents;
};

struct ProofHyp : public ProofExp {
	ProofHyp(Hyp& hy, ProofNode* c, const Subst& s, bool hi);
	ProofHyp(Hyp& hy, ProofNode* c, Subst&& s, bool hi);
	string show() const override;
	bool equal(const ProofNode* n) const override;
	const Term& expr() const override { return expr_; }
	void addParent(ProofNode* p) override { parents.push_back(p); }

	ProofNode* child = nullptr;
	Hyp& node;
	Term expr_;
	vector<ProofNode*> parents;
};

struct ProofRef : public ProofExp {
	ProofRef(Ref& n, ProofExp* c, bool hi);
	string show() const override;
	bool equal(const ProofNode* n) const override;
	const Term& expr() const override {
		if (parent) {
			return parent->expr();
		} else {
			static Term term;
			return term;
		}
	}
	void addParent(ProofNode* p) override {
		if (parent) {
			throw Error("ProofRef parent is already set");
		}
		parent = p;
	}

	Ref& node;
	ProofExp* child = nullptr;
	ProofNode* parent = nullptr;
};

struct ProofProp : public ProofNode {
	ProofProp(Prop& n, const vector<ProofExp*>& p, const Subst& s, bool h);
	string show() const override;
	bool equal(const ProofNode* n) const override;
	const Term& expr() const override { return parent->expr(); }
	void addParent(ProofNode* p) override {
		if (parent) {
			throw Error("ProofProp parent is already set");
		}
		parent = p;
	}

	ProofNode*        parent = nullptr;
	Prop&             node;
	vector<ProofExp*> premises;
private:
	friend void reset_steps(const ProofNode* n);
	mutable rus::Step* step_ = nullptr;
};

struct ProofExpIndexed {
	ProofExp* proof = nullptr;
	uint ind = -1;
	string show() const {
		string ret;
		ret += "index: " + (ind == -1 ? string("-1") : to_string(ind)) + "\n";
		ret += proof->show();
		return ret;
	}
};

struct TheoremProof {
	unique_ptr<rus::Theorem> thm;
	unique_ptr<rus::Proof>   proof;
};

bool unify_down(Prop* pr, Hyp* hy, const vector<ProofExpIndexed>& h);
string show_proof_struct(const ProofNode* n);
unique_ptr<rus::Proof> gen_proof(const ProofNode* n);
TheoremProof gen_theorem_proof(const ProofNode* n);

}}}


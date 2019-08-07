#pragma once

#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

struct ProofNode {
	ProofNode(const Subst& s, bool h) : sub(s), new_(true), ind(global_index()++), hint(h) { }
	ProofNode(Subst&& s, bool h) : sub(std::move(s)), new_(true), ind(global_index()++), hint(h) { }
	explicit ProofNode(const ProofNode& n) = default;
	virtual ~ProofNode() { }
	virtual string show() const = 0;
	virtual bool equal(const ProofNode*) const = 0;
	virtual const Term& expr() const = 0;
	virtual void addParent(ProofNode*) = 0;
	virtual ProofNode* clone() const = 0;

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
	explicit ProofExp(const ProofExp& n) = default;
};

struct ProofTop : public ProofExp {
	ProofTop(const Hyp& n, rus::Hyp* hy, const Subst& s, bool hi);
	ProofTop(const ProofTop& n) :
		ProofExp(n), node(n.node), hyp(n.hyp), expr_(n.expr_) { }
	string show() const override;
	bool equal(const ProofNode* n) const override;
	const Term& expr() const override { return expr_; }
	void addParent(ProofNode* p) override { parents.push_back(p); }
	ProofNode* clone() const override { return new ProofTop(*this); }

	const Hyp& node;
	rus::Hyp*  hyp;
	Term       expr_;
	vector<ProofNode*> parents;
};

struct ProofHyp : public ProofExp {
	ProofHyp(const Hyp& n, ProofNode* c, const Subst& s, bool hi);
	ProofHyp(const Hyp& n, ProofNode* c, Subst&& s, bool hi);
	ProofHyp(const ProofHyp& n) :
		ProofExp(n), node(n.node), child(n.child ? n.child->clone() : nullptr), expr_(n.expr_) {
		child->addParent(this);
	}
	string show() const override;
	bool equal(const ProofNode* n) const override;
	const Term& expr() const override { return expr_; }
	void addParent(ProofNode* p) override { parents.push_back(p); }
	ProofNode* clone() const override {
		return new ProofHyp(*this);
	}

	const Hyp& node;
	ProofNode* child = nullptr;
	Term expr_;
	vector<ProofNode*> parents;
};

struct ProofRef : public ProofExp {
	ProofRef(const Ref& n, ProofExp* c, bool hi);
	ProofRef(const ProofRef& n) :
		ProofExp(n), node(n.node), child(static_cast<ProofExp*>(n.child ? n.child->clone() : nullptr)) {
		child->addParent(this);
	}
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
	ProofNode* clone() const override {
		return new ProofRef(*this);
	}

	const Ref& node;
	ProofExp* child = nullptr;
	ProofNode* parent = nullptr;
};

struct ProofProp : public ProofNode {
	ProofProp(const Prop& n, const vector<ProofExp*>& p, const Subst& s, bool h);
	ProofProp(const ProofProp& n) :
		ProofNode(n), node(n.node) {
		premises.reserve(n.premises.size());
		for (auto p : n.premises) {
			premises.push_back(static_cast<ProofExp*>(p->clone()));
			premises.back()->addParent(this);
		}
	}
	string show() const override;
	bool equal(const ProofNode* n) const override;
	const Term& expr() const override { return parent->expr(); }
	void addParent(ProofNode* p) override {
		if (parent) {
			throw Error("ProofProp parent is already set");
		}
		parent = p;
	}
	ProofNode* clone() const override {
		return new ProofProp(*this);
	}

	const Prop&       node;
	ProofNode*        parent = nullptr;
	vector<ProofExp*> premises;
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

bool unify_down(Prop* pr, Hyp* hy, const vector<ProofExpIndexed>& h);
string show_proof_struct(const ProofNode* n);
unique_ptr<rus::Proof> gen_proof(const ProofNode* n);
void traverseProof(ProofNode* root, std::function<void(ProofNode*)> f);

}}}


#pragma once

#include "rus_prover_proof.hpp"
#include "unify/rus_prover_unify_general.hpp"
#include "unify/rus_prover_unify_index.hpp"
#include "unify/rus_prover_unify_index_term.hpp"

namespace mdl { namespace rus { namespace prover {

struct Tactic {
	virtual ~Tactic() { }
	virtual void add(Prop*) = 0;
	virtual void del(Prop*) = 0;
	virtual Prop* next() = 0;
	virtual string show() const { return ""; }
};

Tactic* make_tactic(const string&);

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

struct Space {
	template<class T>
	using IndexMap = unify::IndexMap<T>;

	Space(Tactic* t) : tactic_(t) { }
	virtual ~Space() { }

	Return init();
	Return info(uint index, string what);
	Return expand(uint index);
	Return erase(uint index);
	Return prove();

	void registerNode(Node* n) {
		n->ind = nodes_.size();
		nodes_.emplace(n->ind, n);
		if (Prop* p = dynamic_cast<Prop*>(n)) {
			tactic_->add(p);
		}
	}
	void unregisterNode(Node* n) {
		nodes_.erase(n->ind);
		if (Prop* p = dynamic_cast<Prop*>(n)) {
			tactic_->del(p);
		}
	}
	uint count() const { return nodes_.size(); }
	Node* getNode(uint i) { return nodes_[i]; }

	virtual void buildUp(Node*) = 0;
	virtual void initProofs(Hyp* h, const rus::Hyp* hint = nullptr) = 0;
	virtual uint theoremId() const = 0;

	vector<unique_ptr<rus::Proof>> proved();
	Return check_proved();
	LightSymbol freshVar(LightSymbol v) {
		auto it = vars.find(v.lit);
		uint fresh = it != vars.end() ? it->second + 1 : LightSymbol::INTERNAL_MIN_INDEX;
		vars[v.lit] = fresh;
		return LightSymbol(v.lit, v.type, ReplMode::KEEP_REPL, fresh);
	}
	const Hyp* root() const { return root_.get(); }
	uint maxProofs() const { return max_proofs; }
	void setMaxProofs(uint mp) { max_proofs = mp; }
	const Tactic* tactic() const { return tactic_.get(); }

protected:
	void completeDown(set<Node*>& downs);

	map<uint, Node*>  nodes_;
	unique_ptr<Hyp>   root_;
	map<uint, uint>   vars;
	unique_ptr<Tactic> tactic_;
	set<uint>          shown;
	uint               max_proofs = -1;
};

}}}


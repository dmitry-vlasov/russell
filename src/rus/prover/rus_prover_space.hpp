#pragma once

#include "rus_prover_node.hpp"
#include "unify/rus_prover_unify_general.hpp"
#include "unify/rus_prover_unify_index.hpp"
#include "unify/rus_prover_unify_index_term.hpp"

namespace mdl { namespace rus { namespace prover {

class Space;

struct Tactic {
	virtual ~Tactic() { }
	virtual void add(Prop*) = 0;
	virtual void del(Prop*) = 0;
	virtual Prop* next() = 0;
};

Tactic* make_tactic(const string&);

struct Space {
	typedef vector<unique_ptr<rus::Proof>> Proved;
	template<class T>
	using IndexMap = unify::IndexMap<T>;

	Space(rus::Qed*, Tactic*);
	Space(rus::Assertion*, rus::Prop*, Tactic*);

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

	Proved proved();
	Return check_proved();

	const IndexMap<HypRef>& hyps() const { return hyps_; }
	const IndexMap<PropRef>& assertions() const { return assertions_; }
	const PropRef& prop() const { return prop_; }
	uint getVar(uint v) const { return vars.at(v); }
	void setVar(uint v, uint i) { vars[v] = i; }
	bool hasVar(uint v) const { return vars.find(v) != vars.end(); }
	const Hyp* root() const { return root_.get(); }
	uint maxProofs() const { return max_proofs; }
	void setMaxProofs(uint mp) { max_proofs = mp; }
	const Assertion* theorem() const { return prop_.ass; }

private:
	map<uint, Node*>  nodes_;
	unique_ptr<Hyp>   root_;
	PropRef           prop_;
	map<uint, uint>   vars;

	IndexMap<HypRef>   hyps_;
	IndexMap<PropRef>  assertions_;
	unique_ptr<Tactic> tactic_;
	set<uint>          shown;
	uint               max_proofs = -1;
};

Return test_with_oracle(string theorem, uint max_proofs, uint max_proof_len);

}}}


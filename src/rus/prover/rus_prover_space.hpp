#pragma once

#include "index/rus_prover_index.hpp"
#include "index/rus_prover_trie_unify_iter.hpp"
#include "rus_prover_show.hpp"
#include "rus_prover_node.hpp"

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
	using TrieIndexMap = index::TrieIndexMap<T>;

	Space(rus::Qed*, Tactic*);
	Space(rus::Assertion*, rus::Prop*, Tactic*);
	~Space() {
		delete root; //TODO: fix
		delete tactic_;
	}

	const uint        ind = 0;
	Proof*            proof = nullptr; // for Oracle tactic
	Hyp*              root;
	PropRef           prop;
	map<uint, uint>   vars;

	TrieIndexMap<HypRef>  hyps_;
	TrieIndexMap<PropRef> assertions_;

	Return init();
	Return info(uint index, string what);
	Return expand(uint index);
	Return erase(uint index);
	Return prove();

	Tactic* getTactic() {
		return tactic_;
	}
	void setTactic(Tactic* t) {
		if (tactic_) delete tactic_;
		tactic_ = t;
	}

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

	map<uint, Node*> nodes_;
	Tactic*          tactic_;
	set<uint>        shown;
	Proved proved();
	Return check_proved();
};

Return test_with_oracle(string theorem);

}}}


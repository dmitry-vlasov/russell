#pragma once

#include "rus_prover_index.hpp"
#include "rus_prover_show.hpp"

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
	Proof*          proof = nullptr; // for Oracle tactic
	Hyp*            root;
	PropRef         prop;
	Index<HypRef>   hyps;
	map<uint, uint> vars;

	Return init();
	Return info(uint index, string what);
	Return expand(uint index);
	Return erase(uint index);

	static bool create(rus::Qed* q, Tactic* t) {
		if (instance) return false;
		instance = new Space(q, t);
		return true;
	}
	static bool create(rus::Assertion* a, rus::Prop* p, Tactic* t) {
		if (instance) return false;
		instance = new Space(a, p, t);
		return true;
	}
	static bool destroy() {
		if (!instance) return false;
		delete instance;
		return true;
	}

	rus::Proof* prove();
	Tactic* getTactic() {
		return tactic_;
	}
	void setTactic(Tactic* t) {
		if (tactic_) delete tactic_;
		tactic_ = t;
	}

	void registerNode(Node* n) {
		n->ind = nodes_.size();
		nodes_.push_back(n);
		if (Prop* p = dynamic_cast<Prop*>(n)) {
			tactic_->add(p);
		}
	}
	void unregisterNode(Node* n) {
		nodes_.erase(nodes_.begin() + n->ind);
		if (Prop* p = dynamic_cast<Prop*>(n)) {
			tactic_->del(p);
		}
	}
	uint count() const { return nodes_.size(); }
	Node* getNode(uint i) { return nodes_[i]; }

	static Space* get() { return instance; }

private:
	Space(rus::Qed*, Tactic*);
	Space(rus::Assertion*, rus::Prop*, Tactic*);
	~Space() { delete root; delete tactic_; }

	vector<Node*> nodes_;
	Tactic*       tactic_;
	set<uint>     shown;
	rus::Proof* checkProved();

	static Space* instance;
};

}}}


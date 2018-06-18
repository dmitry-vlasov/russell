#pragma once

#include "rus_prover_index.hpp"

namespace mdl { namespace rus { namespace prover {

class Space;

struct Tactic {
	virtual ~Tactic() { }
	virtual void add(Node*) = 0;
	virtual void del(Node*) = 0;
	virtual Node* next() = 0;
};

Tactic* make_tactic(string);

struct Space {
	Proof*          proof = nullptr; // for Oracle tactic
	Hyp*            root;
	PropRef         prop;
	Index<HypRef>   hyps;
	map<uint, uint> vars;

	static Return create(rus::Qed* q, Tactic* t) {
		if (instance) return false;
		instance = new Space(q, t);
		string data;
		data += "<tree>\n";
		data += "\t<tree>\n";
		data += "</tree>\n";
		return Return("tree created", data);
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
		tactic_->add(n);
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
	void buildUp(Node*);
	rus::Proof* checkProved();

	static Space* instance;
};

}}}


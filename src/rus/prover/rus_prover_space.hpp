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

struct Space {
	Hyp             root;
	PropRef         prop;
	Index<HypRef>   hyps;
	map<uint, uint> vars;

	Space(rus::Qed*, Tactic*);
	Space(rus::Assertion*, rus::Prop*, Tactic*);
	~Space() { delete tactic_; }
	rus::Proof* prove();
	Tactic* tactic() { return tactic_; }

private:
	Tactic* tactic_;
	void buildUp(Node*);
	rus::Proof* checkProved();
};

}}}


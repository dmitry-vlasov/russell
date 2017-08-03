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
	Tactic*       tactic;
	Hyp           root;
	PropRef       prop;
	Index<HypRef> hyps;
	map<uint, uint> vars;

	Space(rus::Qed*);
	Space(rus::Assertion*, rus::Prop* p);
	rus::Proof* prove();

private:
	void buildUp(Node*);
	rus::Proof* checkProved();
};

}}}


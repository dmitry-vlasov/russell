#pragma once

#include "rus_prover_index.hpp"

namespace mdl { namespace rus { namespace prover {

class Space;

struct Tactic {
	virtual ~Tactic() { }
	virtual void add(Node*) = 0;
	virtual Prop* next() = 0;
};

struct BreadthSearch : public Tactic {
	void add(Node* n) override {
		if (Prop* p = dynamic_cast<Prop*>(n))
			leafs.push(p);
	}
	Prop* next() override {
		Prop* n = leafs.front();
		leafs.pop();
		return n;
	}
private:
	queue<Prop*> leafs;

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
	void buildUp(Prop*);
	void buildUp(Hyp*);
	rus::Proof* checkProved();
};

}}}


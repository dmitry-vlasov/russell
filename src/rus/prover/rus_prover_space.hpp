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

struct BreadthSearch : public Tactic {
	void add(Node* n) override {
		if (Prop* p = dynamic_cast<Prop*>(n))
			leafs.push_back(p);
	}
	void del(Node* n) override {
		if (n) leafs.erase(std::find(leafs.begin(), leafs.end(), n));
	}
	Node* next() override {
		Prop* n = leafs.front();
		leafs.erase(leafs.begin());
		return n;
	}
private:
	vector<Prop*> leafs;
};

struct MetaTactic : public Tactic {
	void add(Node* n) override {
		for (auto t : tactics) t->add(n);
	}
	void del(Node* n) override {
		if (n) for (auto t : tactics) t->del(n);
	}
	Node* next() override {
		return tactics[tactic()]->next();
	}
	virtual uint tactic() = 0;
private:
	vector<Tactic*> tactics;
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


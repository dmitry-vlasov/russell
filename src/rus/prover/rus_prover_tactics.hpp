#pragma once

#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

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

struct Oracle : public Tactic {
	Oracle(rus::Proof*);
	void add(Node* n) override;
	void del(Node* n) override {
		if (n) leafs.erase(std::find(leafs.begin(), leafs.end(), n));
	}
	Node* next() override {
		Prop* n = leafs.front();
		leafs.erase(leafs.begin());
		return n;
	}
private:
	rus::Proof*   proof;
	rus::Step*    root;
	vector<Prop*> leafs;
	map<Prop*, rus::Step*> props;
};

struct MetaTactic : public Tactic {
	~MetaTactic() override {
		for (auto t : tactics) delete t;
	}
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
protected:
	vector<Tactic*> tactics;
};

}}}


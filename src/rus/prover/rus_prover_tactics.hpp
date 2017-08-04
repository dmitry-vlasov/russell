#pragma once

#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

struct QueueTactic : public Tactic {
	void del(Node* n) override {
		if (n) {
			auto it = std::find(leafs.begin(), leafs.end(), n);
			if (it != leafs.end()) leafs.erase(it);
		}
	}
	Node* next() override {
		if (leafs.empty()) return nullptr;
		Prop* n = leafs.front();
		leafs.erase(leafs.begin());
		return n;
	}
protected:
	vector<Prop*> leafs;
};

struct BreadthSearch : public QueueTactic {
	void add(Node* n) override {
		if (Prop* p = dynamic_cast<Prop*>(n))
			leafs.push_back(p);
	}
};

struct Oracle : public QueueTactic {
	Oracle(rus::Proof*);
	void add(Node* n) override;

private:
	rus::Proof*   proof;
	rus::Step*    root;
	map<Prop*, rus::Step*> props;
};

struct ProxyTactic : public Tactic {
	ProxyTactic(Tactic* t, uint m) : tactic(t), mode(m) { }
	~ProxyTactic() { delete tactic; }
	void add(Node* n) override {
		tactic->add(n);
	}
	void del(Node* n) override {
		tactic->del(n);
	}
	Node* next() override {
		Node* n = tactic->next();
		del(n);
		if (n) cout << n->space->root->show(mode) << endl;
		return n;
	}

protected:
	Tactic* tactic;
	uint    mode;
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


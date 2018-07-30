#pragma once

#include <boost/algorithm/string/predicate.hpp>
#include "peglib.h"
#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

struct QueueTactic : public Tactic {
	void del(Prop* n) override {
		if (n) {
			auto it = std::find(leafs.begin(), leafs.end(), n);
			if (it != leafs.end()) {
				leafs.erase(it);
			}
		}
	}
	Prop* next() override {
		if (leafs.empty()) {
			return nullptr;
		}
		Prop* p = leafs.front();
		leafs.erase(leafs.begin());
		return p;
	}
protected:
	vector<Prop*> leafs;
};

struct BreadthSearch : public QueueTactic {
	void add(Prop* p) override {
		leafs.push_back(p);
	}
};

struct Oracle : public QueueTactic {
	Oracle(rus::Proof* = nullptr);
	void add(Prop* p) override;
	void setProof(rus::Proof* p) { proof = p; }

private:
	rus::Proof*   proof;
	rus::Step*    root;
	map<Prop*, rus::Step*> props;
};

struct ProxyTactic : public Tactic {
	ProxyTactic(Tactic* t) : tactic(t) { }
	~ProxyTactic() { delete tactic; }
	void add(Prop* p) override {
		tactic->add(p);
	}
	void del(Prop* p) override {
		tactic->del(p);
	}
	Prop* next() override {
		Prop* p = tactic->next();
		del(p);
		if (p) {
			cout << p->space->root->show() << endl;
		}
		return p;
	}

protected:
	Tactic* tactic;
};

struct MetaTactic : public Tactic {
	MetaTactic(vector<Tactic*>&& t) : tactics(std::move(t)) { }
	~MetaTactic() override {
		for (auto t : tactics) delete t;
	}
	void add(Prop* p) override {
		for (auto t : tactics) t->add(p);
	}
	void del(Prop* p) override {
		if (p) for (auto t : tactics) t->del(p);
	}
	Prop* next() override {
		return tactics[tactic()]->next();
	}
	virtual uint tactic() = 0;
protected:
	vector<Tactic*> tactics;
};

struct AlterTactic : public MetaTactic {
	AlterTactic(vector<Tactic*>&& t) : MetaTactic(std::move(t)) { }
	uint tactic() override {
		if (index + 1 == tactics.size()) index = 0;
		else ++ index;
		return index;
	}
private:
	uint index = 0;
};

}}}


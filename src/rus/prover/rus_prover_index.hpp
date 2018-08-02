#pragma once

#include "rus_prover_expr.hpp"
#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

struct Index {
	typedef set<uint> LeafInds;
	struct Node {
		LeafInds leafs;
		vector<unique_ptr<Index>> child;
	};
	typedef map<uint, pair<Subst, Subst>> Unified;

	map<const Rule*, Node> rules;
	map<LightSymbol, LeafInds> vars;
	uint size = 0;

	uint add(const LightTree& t) {
		uint ind = size++;
		add(t, ind);
		return ind;
	}
	void add(const LightTree& t, uint s);
	Unified match_forth(const LightTree& t) const;
	Unified match_back(const LightTree& t) const;

	string show() const;
};

template<class Data>
struct UnifyMap {
	struct Unified {
		Unified(const Data& d, pair<Subst, Subst>&& s) : data(d), subs(std::move(s)) { }
		Data data;
		pair<Subst, Subst> subs;
	};
	void add(const LightTree& t, const Data& d) {
		index.add(t);
		data.push_back(d);
	}
	vector<Unified> match_forth(const LightTree& t) {
		vector<Unified> ret;
		Index::Unified unif = index.match_forth(t);
		for (auto& p : unif) {
			ret.emplace_back(data[p.first], std::move(p.second));
		}
		return ret;
	}
	vector<Unified> match_back(const LightTree& t) {
		vector<Unified> ret;
		Index::Unified unif = index.match_back(t);
		for (auto& p : unif) {
			ret.emplace_back(data[p.first], std::move(p.second));
		}
		return ret;
	}
	string show() const {
		return index.show();
	}

private:
	Index index;
	vector<Data> data;
};

}}}


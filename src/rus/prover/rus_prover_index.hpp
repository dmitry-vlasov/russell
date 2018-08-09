#pragma once

#include "rus_prover_unify.hpp"
#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

struct Index {
	typedef set<uint> LeafInds;
	struct Node {
		LeafInds leafs;
		vector<unique_ptr<Index>> child;
	};
	typedef map<uint, prover::Unified> Unified;

	map<const Rule*, Node> rules;
	map<LightSymbol, LeafInds> vars;
	uint size = 0;

	uint add(const LightTree&);
	Index::Unified unify(const LightTree&) const;
	string show() const;

	vector<LightTree> exprs;
};


template<class Data>
struct UnifyMap {
	struct Unified {
		Unified(const Data& d, prover::Unified&& u) : data(d), unif(std::move(u)) { }
		Data  data;
		prover::Unified unif;
	};
	void add(const LightTree& t, const Data& d) {
		index.add(t);
		data.push_back(d);
	}
	vector<Unified> unify(const LightTree& t) {
		vector<Unified> ret;
		Index::Unified unif = index.unify(t);
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


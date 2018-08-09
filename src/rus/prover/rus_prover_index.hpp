#pragma once

#include "rus_prover_unify.hpp"
#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

struct Index {
	typedef set<uint> LeafInds;
	struct Node {
		bool is_leaf() const { return !child.size(); }
		LeafInds leafs;
		vector<unique_ptr<Index>> child;
	};
	typedef map<uint, Subst> Unified;

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
		Unified(const Data& d, Subst&& s) : data(d), sub(std::move(s)) { }
		Data  data;
		Subst sub;
	};
	void add(const LightTree& t, const Data& d) {
		index.add(t);
		data.push_back(d);
	}
	vector<Unified> unify(const LightTree& t) {
		vector<Unified> ret;
		Index::Unified unif = index.unify(t);
		for (auto& p : unif) {
			if (p.second.ok) {
				//cout << "UnifyMap ind: " << p.first << endl;
				ret.emplace_back(data[p.first], std::move(p.second));
			}
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


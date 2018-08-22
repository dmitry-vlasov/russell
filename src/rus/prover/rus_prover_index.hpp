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
	Unified unify(const LightTree&) const;
	string show() const;

	vector<LightTree> exprs;
};


template<class Data>
struct IndexMap {
	struct Unified {
		Unified(const Data& d, Subst&& s) : data(d), sub(std::move(s)) { }
		Data  data;
		Subst sub;
	};
	void add(const LightTree& t, const Data& d) {
		index_.add(t);
		data_.push_back(d);
	}
	vector<Unified> unify(const LightTree& t) {
		vector<Unified> ret;
		Index::Unified unif = index_.unify(t);
		for (auto& p : unif) {
			if (p.second.ok) {
				ret.emplace_back(data_[p.first], std::move(p.second));
			}
		}
		return ret;
	}
	string show() const {
		return index_.show();
	}

	const Index& index() const { return index_; }
	const vector<Data>& data() const { return data_; }

private:
	Index index_;
	vector<Data> data_;
};

typedef IndexMap<uint> IndexInt;

extern bool debug_index;
extern bool debug_ind;

}}}


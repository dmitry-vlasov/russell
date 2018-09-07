#pragma once

#include "rus_prover_product_vector.hpp"

namespace mdl { namespace rus { namespace prover {

typedef map<vector<uint>, Subst> MultyUnifiedSubs;

struct SubstTree {
	Subst     sub;
	LightTree tree;
	string show() const;
};

template<class Data>
struct VectorMap {
	map<vector<uint>, Data> map_;
};

template<class D>
VectorMap<vector<D>> intersect(const vector<const VectorMap<D>*>& v) {
	VectorMap<vector<D>> ret;
	for (const auto& p : v[0]->map_) {
		vector<uint> k = p.first;
		vector<D> data;
		for (const auto& m : v) {
			auto i = m->map_.find(k);
			if (i != m->map_.end() && i->second.sub.ok) {
				data.push_back(i->second);
			} else {
				break;
			}
		}
		if (data.size() == v.size()) {
			ret.map_[k] = data;
		}
	}
	return ret;
}

struct VectorUnified {
	string show() const;
	void finalize(ProdVect leafs_vect, const vector<LightSymbol>& w, const LightTree& t);
	void add_intersection(const vector<VectorUnified>& v, const Rule* r, const vector<LightSymbol>& w);
	void finalize(const vector<uint> leafs, const vector<LightSymbol>& w, const LightTree& t);

	std::map<vector<uint>, SubstTree>& map() { return unif_.map_; }
	const std::map<vector<uint>, SubstTree>& map() const { return unif_.map_; }

private:
	CartesianProd<uint> leafsProd(const ProdVect& leafs);
	friend MultyUnifiedSubs intersect(const std::map<LightSymbol, VectorUnified>& terms, MultyUnifiedSubs& unif);

	VectorMap<SubstTree> unif_;
};

 MultyUnifiedSubs intersect(const map<LightSymbol, VectorUnified>& terms, MultyUnifiedSubs& unif);

}}}


#pragma once

#include "rus_prover_product_vector.hpp"

namespace mdl { namespace rus { namespace prover {

template<class Data>
struct VectorMap {
	VectorMap(bool f = false) : full(f) { }
	VectorMap(const VectorMap&) = default;
	VectorMap& operator = (const VectorMap&) = default;

	bool full;
	map<vector<uint>, Data> map_;
};

template<class D>
void intersect(VectorMap<vector<D>>& v, const VectorMap<D>& w) {
	if (v.full) {
		for (const auto& p : w.map_) {
			v.map_[p.first].push_back(p.second);
		}
	} else {
		map<vector<uint>, vector<D>> new_map_;
		for (const auto& p : v.map_) {
			vector<uint> k = p.first;
			vector<D> data = p.second;
			auto i = w.map_.find(k);
			if (i != w.map_.end() && i->second.sub.ok) {
				data.push_back(i->second);
				new_map_[k] = data;
			}
		}
		v.map_ = new_map_;
	}
}

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

template<class D, class F>
VectorMap<vector<D>> intersect_func(const vector<const VectorMap<D>*>& v) {
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

typedef map<vector<uint>, Subst> MultyUnifiedSubs;

struct SubstTree {
	Subst     sub;
	LightTree tree;
	string show() const;
};

struct VectorUnified {
	string show() const;
	void finalize(ProdVect leafs_vect, const vector<LightSymbol>& w, const LightTree& t);
	void add_intersection(const vector<VectorUnified>& v, const Rule* r, const vector<LightSymbol>& w);

	std::map<vector<uint>, SubstTree>& map() { return unif_.map_; }
	const std::map<vector<uint>, SubstTree>& map() const { return unif_.map_; }

private:
	void finalize(const vector<uint> leafs, const vector<LightSymbol>& w, const LightTree& t);
	CartesianProd<uint> leafsProd(const ProdVect& leafs);
	friend MultyUnifiedSubs intersect(const std::map<LightSymbol, VectorUnified>& terms, MultyUnifiedSubs& unif);

	VectorMap<SubstTree> unif_;
};

 MultyUnifiedSubs intersect(const map<LightSymbol, VectorUnified>& terms, MultyUnifiedSubs& unif);

}}}


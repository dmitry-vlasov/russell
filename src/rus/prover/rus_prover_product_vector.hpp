#pragma once

#include "rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover {

inline set<uint> intersect(const set<uint>& s1, const set<uint>& s2, bool& empty) {
	set<uint> ret;
	empty = true;
	for (uint i : s1) {
		if (s2.find(i) != s2.end()) {
			ret.insert(i);
			empty = false;
		}
	}
	return ret;
}

inline vector<set<uint>> intersect(const vector<set<uint>>& v1, const vector<set<uint>>& v2, bool& empty) {
	vector<set<uint>> ret(v1.size());
	for (uint i = 0; i < v1.size(); ++ i) {
		ret[i] = intersect(v1[i], v2[i], empty);
		if (empty) {
			break;
		}
	}
	return ret;
}

template<class Data>
struct ProdVectData {
	vector<set<uint>> prod_vect;
	Data data;
};

template<class Data>
struct ProdVectMap {
	vector<ProdVectData<Data>> map;
};

template<class D>
ProdVectMap<pair<D, D>> intersect(const ProdVectMap<D>& m1, const ProdVectMap<D>& m2) {
	ProdVectMap<D> ret;
	for (const auto& d1 : m1.map) {
		for (const auto& d2 : m1.map) {
			bool empty;
			vector<set<uint>> is = intersect(d1.prod_vect, d2.prod_vect, empty);
			if (!empty) {
				ret.map.emplace_back({is, pair<D, D>(d1.data, d2.data)});
			}
		}
	}
	return ret;
}

}}}

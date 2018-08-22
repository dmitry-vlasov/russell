#pragma once

#include "rus_prover_vector_index.hpp"

namespace mdl { namespace rus { namespace prover {




inline set<uint> complement(const set<uint>& s, uint m) {
	set<uint> ret;
	for (uint i = 0; i < m; ++ i) {
		if (!s.count(i)) {
			ret.insert(i);
		}
	}
	return ret;
}

inline bool are_complement(const set<uint>& s1, set<uint>& s2, uint m) {
	for (uint i = 0; i < m; ++ i) {
		if (s1.count(i) + s2.count(i) != 1) {
			return false;
		}
	}
	return true;
}

inline vector<uint> reduce_leafs(const vector<uint>& leafs, const set<uint>& s) {
	vector<uint> ret;
	for (uint i = 0 ; i < leafs.size(); ++ i) {
		if (s.count(i)) {
			ret.push_back(leafs[i]);
		}
	}
	return ret;
}

inline vector<uint> join_leafs(const vector<uint>& leafs1, const vector<uint>& leafs2, const set<uint>& s) {
	vector<uint> ret;
	for (uint i = 0, n = 0, m = 0 ; i < leafs1.size() + leafs2.size(); ++ i) {
		if (s.count(i)) {
			ret.push_back(leafs1[n++]);
		} else {
			ret.push_back(leafs2[m++]);
		}
	}
	return ret;
}

inline MultyUnifiedSubs reduce_subs(const MultyUnifiedSubs& subs, const set<uint>& s) {
	MultyUnifiedSubs ret;
	for (const auto& p : subs) {
		ret[reduce_leafs(p.first, s)] = p.second;
	}
	return ret;
}

inline MultyUnifiedSubs join_subs(const MultyUnifiedSubs& subs1, const MultyUnifiedSubs& subs2, const set<uint>& s) {
	MultyUnifiedSubs ret;
	for (const auto& p : subs2) {
		ret[reduce_leafs(p.first, s)] = p.second;
	}
	return ret;
}

inline Restrictions reduce_restrictions(const Restrictions& restrictions, const set<uint>& s) {
	Restrictions ret;
	for (const auto& leafs : restrictions) {
		ret.insert(reduce_leafs(leafs, s));
	}
	return ret;
}

}}}


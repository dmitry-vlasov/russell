#pragma once

#include "rus_prover_vector_index.hpp"

namespace mdl { namespace rus { namespace prover {




inline vector<uint> complement(const vector<uint>& s) {
	vector<uint> ret;
	for (uint i = 0; i < s.size(); ++ i) {
		ret.push_back((s[i] == -1) ? 0 : -1);
	}
	return ret;
}

inline uint active_size(const vector<uint>& s) {
	uint ret = 0;
	for (uint i = 0; i < s.size(); ++ i) {
		ret += ((s[i] == -1) ? 0 : 1);
	}
	return ret;
}

inline bool are_complement(const vector<uint>& s1, const vector<uint>& s2) {
	if (s1.size() != s2.size()) {
		return false;
	}
	for (uint i = 0; i < s1.size(); ++ i) {
		if ((s1[1] == -1) != (s2[i] == -1)) {
			return false;
		}
	}
	return true;
}

inline vector<uint> reduce_leafs(const vector<uint>& leafs1, const vector<uint>& leafs2) {
	vector<uint> ret;
	for (uint i = 0 ; i < leafs1.size(); ++ i) {
		if (leafs2[i] == -1) {
			ret.push_back(-1);
		} else {
			ret.push_back(leafs1[i]);
		}
	}
	return ret;
}

inline vector<uint> join_leafs(const vector<uint>& leafs1, const vector<uint>& leafs2) {
	vector<uint> ret;
	for (uint n = 0, m = 0 ; n + m < leafs1.size() + leafs2.size();) {
		if (leafs1[n] != -1) {
			ret.push_back(leafs1[n++]);
		} else {
			ret.push_back(leafs2[m++]);
		}
	}
	return ret;
}

inline MultyUnifiedSubs reduce_subs(const MultyUnifiedSubs& subs, const vector<uint>& s) {
	MultyUnifiedSubs ret;
	for (const auto& p : subs) {
		ret[reduce_leafs(p.first, s)] = p.second;
	}
	return ret;
}

inline Restrictions reduce_restrictions(const Restrictions& restrictions, const vector<uint>& s) {
	Restrictions ret;
	for (const auto& leafs : restrictions) {
		ret.insert(reduce_leafs(leafs, s));
	}
	return ret;
}

}}}


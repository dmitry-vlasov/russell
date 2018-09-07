#pragma once

#include "rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover {

struct Set {
	Set(bool i = false) : init_(i), index_leafs(nullptr) { }
	Set(const Set&) = default;
	Set& operator = (const Set&) = default;

	bool init(const Index::Leaf& ind_leafs, const vector<uint>* ind_values) {
		if (!index_leafs) {
			index_leafs = &ind_leafs;
			for (uint s : ind_leafs.inds) {
				set_.insert(ind_values->at(s));
			}
			init_ = true;
			return true;
		} else {
			return index_leafs == &ind_leafs;
		}
	}

	void init(const vector<uint>& l) {
		init_ = true;
		for (auto i : l) {
			set_.insert(i);
		}
	}

	string show() const {
		if (!init_) {
			return "?";
		} else if (!set_.size()) {
			return "emtpy";
		} else if (set_.size() == 1) {
			return to_string(*set_.begin());
		} else {
			string ret;
			ret += "{";
			bool first = true;
			for (auto i : set_) {
				if (!first) {
					ret += ", ";
				}
				ret += to_string(i);
				first = false;
			}
			ret += "}";
			return ret;
		}
	}

	bool storesInfo() const {
		return init_ && set_.size() > 0;
	}

	const std::set<uint>& set() const {
		return set_;
	}

	bool is_init() const {
		return init_;
	}

private:
	friend Set intersect(const Set& s1, const Set& s2);

	std::set<uint> set_;
	bool init_;
	const Index::Leaf* index_leafs;
};

inline Set intersect(const Set& s1, const Set& s2) {
	if (!(s1.init_ && s2.init_)) {
		return Set();
	}
	Set ret(true);
	for (uint i : s1.set_) {
		if (s2.set_.find(i) != s2.set_.end()) {
			ret.set_.insert(i);
		}
	}
	return ret;
}

struct ProdVect {
	ProdVect(uint s = 1) : vect(s) { }
	ProdVect(const ProdVect&) = default;
	ProdVect& operator = (const ProdVect&) = default;

	bool empty() const {
		for (const auto& s : vect) {
			if (!s.set().size()) {
				return true;
			}
		}
		return false;
	}
	bool storesInfo() const {
		for (const auto& s : vect) {
			if (!s.storesInfo()) {
				return false;
			}
		}
		return true;
	}
	bool defined() const {
		for (const auto& s : vect) {
			if (!s.is_init()) {
				return false;
			}
		}
		return true;
	}
	string show() const {
		string ret;
		ret += "(";
		bool first = true;
		for (const auto& s : vect) {
			if (!first) {
				ret += ", ";
			}
			ret += s.show();
		}
		ret += ")";
		return ret;
	}
	vector<Set> vect;
};

inline ProdVect intersect(const ProdVect& v1, const ProdVect& v2) {
	assert(v1.vect.size() == v2.vect.size() && "intersect: v1.vect.size() != v2.vect.size()");
	ProdVect ret(v1.vect.size());
	for (uint i = 0; i < v1.vect.size(); ++ i) {
		ret.vect[i] = intersect(v1.vect[i], v2.vect[i]);
	}
	return ret;
}



template<class Data>
struct ProdVectData {
	ProdVect prod;
	Data data;

	string show() const {
		return prod.show() + " --> " + data.show();
	}
};

template<class Data>
struct ProdVectMap {
	vector<ProdVectData<Data>> map;

	string show() const {
		string ret;
		for (const auto& pvd : map) {
			ret += pvd.show() + "\n";
		}
		return ret;
	}
	std::map<vector<uint>, Data> transform() const {
		std::map<vector<uint>, Data> ret;

		return ret;
	}
};

template<class D>
ProdVectMap<pair<D, D>> intersect(const ProdVectMap<D>& m1, const ProdVectMap<D>& m2) {
	ProdVectMap<D> ret;
	for (const auto& d1 : m1.map) {
		for (const auto& d2 : m1.map) {;
			ProdVect pv = intersect(d1.prod.vect, d2.prod.vect);
			if (!pv.empty()) {
				ret.map.emplace_back({pv, pair<D, D>(d1.data, d2.data)});
			}
		}
	}
	return ret;
}


}}}

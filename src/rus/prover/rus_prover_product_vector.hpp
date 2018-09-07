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

	bool is_subset_of(const Set& s) const {
		if (!init_) return false;
		for (auto i : set_) {
			if (s.set_.find(i) == s.set_.end()) {
				return false;
			}
		}
		return true;
	}

	void unite(const Set& s) {
		if (!(init_ && s.init_)) return;
		for (uint i : s.set_) set_.insert(i);
	}

	void intersect(const Set& s) {
		if (!(init_ && s.init_)) return;
		for (uint i : set_) if (s.set_.find(i) == s.set_.end()) set_.erase(i);
	}

private:
	friend Set prover::intersect(const Set& s1, const Set& s2);
	friend Set prover::unite(const Set& s1, const Set& s2);

	std::set<uint> set_;
	bool init_;
	const Index::Leaf* index_leafs;
};

inline Set intersect(const Set& s1, const Set& s2) {
	Set s(s1); s.intersect(s2); return s;
}

inline Set unite(const Set& s1, const Set& s2) {
	Set s(s1); s.unite(s2); return s;
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

	void intersect(const ProdVect& v) {
		assert(vect.size() == v.vect.size() && "intersect: vect.size() != v.vect.size()");
		for (uint i = 0; i < vect.size(); ++ i) {
			vect[i].intersect(v.vect[i]);
		}
	}
	Set& operator[] (uint i) { return vect[i]; }
	const Set& operator[] (uint i) const { return vect[i]; }

	vector<Set> vect;
};

inline ProdVect intersect(const ProdVect& v1, const ProdVect& v2) {
	ProdVect ret(v1); ret.intersect(v2); return ret;
}

struct UnionVect {
	bool is_superset_of(const ProdVect& v) {
		for (uint i = 0; i < v.vect.size(); ++ i) {
			Set u(un[0].vect[i]);
			for (uint j = 1; j < un.size(); ++ j) {
				u.unite(un[j].vect[j]);
			}
			if (!v.vect[i].is_subset_of(u)) {
				return false;
			}
		}
		return true;
	}
	string show() const {
		string ret;
		ret += "{\n";
		for (const auto& s : un) {
			ret += "\t" + s.show() + "\n";
		}
		ret += "}\n";
		return ret;
	}
	void intersect(const ProdVect& v) {
		vector<uint> empty_components;
		for (uint i = 0; i < un.size(); ++i) {
			un[i].intersect(v);
			if (!un[i].storesInfo()) {
				empty_components.push_back(i);
			}
		}
		//if ()
	}
	vector<ProdVect> un;
};

struct DiffVect {
	ProdVect positive;
	UnionVect negative;

	void intersect(const ProdVect& v) {
		positive.intersect(v);
		negative.intersect(v);
	}
	void subtract(const ProdVect& v) {

	}
};

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

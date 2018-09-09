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

	bool intersects_with(const Set& s) const {
		if (!init_ && !s.init_) {
			return true;
		} else if (init_ && s.init_) {
			for (uint i : set_) {
				if (s.set_.find(i) == s.set_.end()) {
					return true;
				}
			}
			return false;
		} else {
			return false;
		}
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

	bool intersects_with(const ProdVect& v) const {
		assert(vect.size() == v.vect.size() && "intersect: vect.size() != v.vect.size()");
		for (uint i = 0; i < vect.size(); ++ i) {
			if (!vect[i].intersects_with(v.vect[i])) {
				return false;
			}
		}
		return true;
	}

	Set& operator[] (uint i) { return vect[i]; }
	const Set& operator[] (uint i) const { return vect[i]; }

	vector<Set> vect;
};

inline ProdVect intersect(const ProdVect& v1, const ProdVect& v2) {
	ProdVect ret(v1); ret.intersect(v2); return ret;
}

template<class Data>
struct UnionVect {
	UnionVect(uint d, bool f = false) : dim(d), full(f) { }

	struct Pair {
		ProdVect key;
		Data     value;
		string show() const {
			ostringstream oss;
			oss << key.show() << " --> " << value.show();
			return oss.str();
		}
	};
	string show() const {
		ostringstream oss;
		oss << "{" << endl;
		for (const auto& s : un) {
			oss << "\t" << s.show() << endl;
		}
		oss << "}" << endl;
		return oss.str();
	}
	void intersect(const ProdVect& v) {
		vector<Pair> new_un;
		for (const auto& p : un) {
			p.key.intersect(v);
			if (p.key.storesInfo()) {
				new_un.push_back(p);
			}
		}
		un = new_un;
	}

	void unite(const UnionVect& u) {
		for (const auto& v : u.un) {
			un.push_back(v);
		}
	}
	bool empty() const {
		return un.empty();
	}

	vector<Pair> un;
	uint dim;
	bool full;
};

template<class D>
UnionVect<vector<D>> intersect(const UnionVect<vector<D>>& v, const UnionVect<D>& uv) {
	UnionVect<vector<D>> ret;
	if (v.full) {
		for (const auto& p : uv.un) {
			ret.un.emplace_back(p.first, {p.second});
		}
	} else {
		for (uint i = 0; i < v.un.size(); ++ i) {
			const ProdVect& k = v.un[i].key;
			vector<D> data;
			for (uint j = 1; j < uv.size(); ++j) {


			}
			if (data.size() == uv.size()) {
				ret.map_[k] = data;
			}
		}
	}
	return ret;
}

}}}

#pragma once

#include <list>
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

	void complement(const Set& s) {
		if (!(init_ && s.init_)) return;
		for (uint i : set_) if (s.set_.find(i) != s.set_.end()) set_.erase(i);
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

	void complement(const ProdVect& v) {
		assert(vect.size() == v.vect.size() && "intersect: vect.size() != v.vect.size()");
		for (uint i = 0; i < vect.size(); ++ i) {
			vect[i].complement(v.vect[i]);
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

inline ProdVect complement(const ProdVect& v1, const ProdVect& v2) {
	ProdVect ret(v1); ret.complement(v2); return ret;
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
	bool empty() const {
		return un.empty();
	}

	std::list<Pair> un;
	uint dim;
	bool full;
};

template<class D>
UnionVect<vector<D>> intersect(const UnionVect<vector<D>>& v, const UnionVect<D>& uv) {
	UnionVect<vector<D>> ret;
	if (v.full) {
		for (const auto& p : uv.un) {
			ret.un.emplace_back(p.key, {p.value});
		}
	} else {
		for (const auto& p : v.un) {
			for (const auto& q : uv.un) {
				ProdVect r = intersect(p, q);
				if (r.storesInfo() && q.value.sub.ok) {
					vector<D> data = p.value;
					data.push_back(q.value);
					ret.un.emplace_back(r, data);
				}
			}
		}
	}
	return ret;
}

inline vector<ProdVect> split(const ProdVect& v, const ProdVect& inter) {
	ProdVect comp = complement(v, inter);
	if (!comp.storesInfo()) {
		return {v};
	}
	vector<ProdVect> ret;
	PowerSetIter iter;
	for (uint i = 0; i < v.vect.size(); ++i) {
		if (v[i].is_init()) {
			iter.addDim();
		} else {
			iter.addSkipped();
		}
	}
	while (true) {
		if (!iter.initial()) {
			ProdVect pv(v.vect.size());
			for (uint i = 0; i < pv.vect.size(); ++ i) {
				if (iter[i]) {
					pv[i] = comp[i];
				} else {
					pv[i] = inter[i];
				}
			}
			ret.push_back(pv);
		}
		if (!iter.hasNext()) {
			break;
		}
		iter.makeNext();
	}
	return ret;
}

template<class D>
UnionVect<vector<D>> unite(const UnionVect<vector<D>>& uv1, const UnionVect<D>& uv2) {
	UnionVect<vector<D>> ret;
	stack<typename UnionVect<D>::Pair> to_add;
	for (const auto& p : uv2.un) {
		to_add.push(p);
	}
	while (!to_add.empty()) {
		const typename UnionVect<D>::Pair& q = to_add.top(); to_add.pop();
		bool intersects = false;
		for (const auto& p : uv1.un) {
			if (p.key.intersects_with(q.key)) {
				intersects = true;
				ProdVect inter = intersect(p.key, q.key);
				for (const auto& part : split(p.key, inter)) {
					ret.un.emplace_back(part, {p.vaue, q.value});
				}
				for (const auto& part : split(q.key, inter)) {
					to_add.push(part, q.value);
				}
			}
		}
		if (!intersects) {
			ret.un.push_back(q);
		}
	}
	return ret;
}

}}}

#pragma once

#include <list>
#include "rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover {

struct Set {
	Set(bool i = false) : init_(i), index_leafs(nullptr) { }
	Set(const Set&) = default;
	Set& operator = (const Set&) = default;

	bool operator == (const Set& s) const {
		return set_ == s.set_ && init_ == s.init_;
	}
	bool operator != (const Set& s) const {
		return !operator == (s);
	}

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
		} else if (set_.size() == 0) {
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
				if (s.set_.find(i) != s.set_.end()) {
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

	bool operator == (const ProdVect& v) const {
		for (uint i = 0; i < vect.size(); ++ i) {
			if (vect[i] != v.vect[i]) {
				return false;
			}
		}
		return true;
	}
	bool operator != (const ProdVect& v) const {
		return !operator == (v);
	}

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
			first = false;
		}
		ret += ")";
		return ret;
	}

	void intersect(const ProdVect& v) {
		if (vect.size() != v.vect.size()) {
			cout << "vect.size() != v.vect.size(): " << vect.size() << " !=  " << v.vect.size() << endl;
		}
		assert(vect.size() == v.vect.size() && "intersect: vect.size() != v.vect.size()");
		for (uint i = 0; i < vect.size(); ++ i) {
			vect[i].intersect(v.vect[i]);
		}
	}

	void complement(const ProdVect& v) {
		if (vect.size() != v.vect.size()) {
			cout << "vect.size() != v.vect.size(): " << vect.size() << " !=  " << v.vect.size() << endl;
		}
		assert(vect.size() == v.vect.size() && "intersect: vect.size() != v.vect.size()");
		for (uint i = 0; i < vect.size(); ++ i) {
			vect[i].complement(v.vect[i]);
		}
	}

	bool intersects_with(const ProdVect& v) const {
		if (vect.size() != v.vect.size()) {
			cout << "vect.size() != v.vect.size(): " << vect.size() << " !=  " << v.vect.size() << endl;
			cout << "vect: " << show() << endl;
			cout << "v.vect: " << v.show() << endl;
			throw Error("vect.size() != v.vect.size():");
		}
		//assert(vect.size() == v.vect.size() && "intersect: vect.size() != v.vect.size()");
		for (uint i = 0; i < vect.size(); ++ i) {
			if (!vect[i].intersects_with(v.vect[i])) {
				return false;
			}
		}
		return true;
	}

	vector<vector<uint>> unfold() const {
		vector<vector<uint>> ret;
		CartesianProd<uint> prod;
		for (uint i = 0; i < vect.size(); ++ i) {
			assert(vect[i].is_init() && vect[i].set().size());
			prod.addDim(vect[i].set());
		}
		if (prod.card() > 0) {
			while (true) {
				ret.push_back(prod.data());
				if (!prod.hasNext()) {
					break;
				}
				prod.makeNext();
			}
		}
		return ret;
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

inline vector<ProdVect> split(const ProdVect& v, const ProdVect& inter) {
	ProdVect comp = complement(v, inter);
	if (!comp.storesInfo()) {
		return vector<ProdVect>();
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

struct SubstTree {
	Subst     sub;
	LightTree tree;
	string show() const;
};



template<class Data>
struct UnionVect {
	UnionVect(bool f = false) : full(f) { }

	struct Pair {
		Pair(const ProdVect& k, const Data& v) : key(k), value(v) { }
		Pair(const Pair&) = default;
		Pair& operator = (const Pair&) = default;
		ProdVect key;
		Data     value;
		string show() const {
			ostringstream oss;
			oss << key.show() << " --> "; // << value.show();
			return oss.str();
		}
	};
	string show() const {
		if (un.empty()) {
			return "{ }";
		}
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
	void add(const ProdVect& k, const Data& v) {
		un.emplace_back(k, v);
	}
	bool hasKey(const ProdVect& k) const {
		for (const auto& p : un) {
			if (p.key == k) {
				return true;
			}
		}
		return false;
	}

	bool check_uniqueness() const {
		for (auto pi = un.begin(); pi != un.end(); ++pi) {
			for (auto qi = un.begin(); qi != un.end(); ++qi) {
				if (pi != qi && pi->key == qi->key) {
					cout << "duplicate key: " << pi->key.show() << endl;
					return false;
				}
			}
		}
		return true;
	}

	void unite(const ProdVect& pv, auto finalizer) {
		stack<ProdVect> to_add;
		to_add.emplace(pv);
		while (!to_add.empty()) {
			ProdVect q = to_add.top(); to_add.pop();
			bool intersects = false;
			auto pi = un.begin();
			while (pi != un.end()) {
				if (pi->key.intersects_with(q)) {
					intersects = true;
					ProdVect inter = intersect(pi->key, q);
					for (const auto& part : split(pi->key, inter)) {
						SubstTree st = pi->value;
						finalizer(st);
						un.emplace_back(part, st);
					}
					for (const auto& part : split(q, inter)) {
						to_add.emplace(part);
					}
					pi = un.erase(pi);
				} else {
					++pi;
				}
			}
			if (!intersects) {
				SubstTree st;
				finalizer(st);
				un.emplace_back(q, st);
			}
		}
	}

	const std::list<Pair>& un__() const { return un; }

private:
	template<class D> friend UnionVect<vector<D>> intersect(const UnionVect<vector<D>>&, const UnionVect<D>&);

	std::list<Pair> un;
	bool full;
};

template<class D>
UnionVect<vector<D>> intersect(const UnionVect<vector<D>>& v, const UnionVect<D>& uv) {
	UnionVect<vector<D>> ret;
	if (v.full) {
		for (const auto& p : uv.un) {
			ret.un.emplace_back(p.key, vector<D>(1, p.value));
		}
	} else {
		for (const auto& p : v.un) {
			for (const auto& q : uv.un) {
				ProdVect r = intersect(p.key, q.key);
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

typedef map<vector<uint>, Subst> MultyUnifiedSubs;

}}}

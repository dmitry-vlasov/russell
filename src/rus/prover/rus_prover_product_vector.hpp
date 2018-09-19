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
	friend Set prover::complement(const Set& s1, const Set& s2);

	std::set<uint> set_;
	bool init_;
	const Index::Leaf* index_leafs;
};

inline Set intersect(const Set& s1, const Set& s2) {
	if (s1.set_.size() > s2.set_.size()) {
		return intersect(s2, s1);
	}
	assert(s1.init_ == s2.init_);
	Set s(s1.init_);
	if (s1.init_ && s2.init_) {;
		for (uint i : s1.set_) {
			if (s2.set_.find(i) != s2.set_.end()) {
				s.set_.insert(i);
			}
		}
	}
	return s;
}

inline set<uint> intersect(const set<uint>& s1, const set<uint>& s2) {
	if (s1.size() > s2.size()) {
		return intersect(s2, s1);
	}
	set<uint> s;
	for (uint i : s1) {
		if (s2.find(i) != s2.end()) {
			s.insert(i);
		}
	}
	return s;
}

inline Set complement(const Set& s1, const Set& s2) {
	assert(s1.init_ == s2.init_);
	Set s(s1.init_);
	if (s1.init_ && s2.init_) {;
		for (uint i : s1.set_) {
			if (s2.set_.find(i) == s2.set_.end()) {
				s.set_.insert(i);
			}
		}
	}
	return s;
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
			vect[i] = prover::intersect(vect[i], v.vect[i]);
		}
	}

	void complement(const ProdVect& v) {
		if (vect.size() != v.vect.size()) {
			cout << "vect.size() != v.vect.size(): " << vect.size() << " !=  " << v.vect.size() << endl;
		}
		assert(vect.size() == v.vect.size() && "intersect: vect.size() != v.vect.size()");
		for (uint i = 0; i < vect.size(); ++ i) {
			vect[i] = prover::complement(vect[i], v.vect[i]);
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
		if (storesInfo()) {
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

inline bool intersects(const set<vector<uint>>& s1, const set<vector<uint>>& s2) {
	for (const auto v : s1) {
		if (s2.count(v)) {
			return true;
		}
	}
	return false;
}

inline bool is_splitting(const ProdVect& v, const vector<ProdVect>& s, const ProdVect& i) {
	set<vector<uint>> s1;
	for (const auto& p : v.unfold()) {
		s1.insert(p);
	}
	set<vector<uint>> s2;
	vector<set<vector<uint>>> parts;
	parts.push_back(set<vector<uint>>());
	for (const auto& p : i.unfold()) {
		s2.insert(p);
		parts.back().insert(p);
	}
	for (const auto& w : s) {
		if (!w.storesInfo() || w == i) {
			return false;
		}
		parts.push_back(set<vector<uint>>());
		for (const auto& p : w.unfold()) {
			s2.insert(p);
			parts.back().insert(p);
		}
	}
	for (auto ip = parts.begin(); ip != parts.end(); ++ip) {
		for (auto jp = parts.begin(); jp != parts.end(); ++jp) {
			if (ip != jp) {
				if (intersects(*ip, *jp)) {
					return false;
				}
			}
		}
	}
	return s1 == s2;
}

inline vector<ProdVect> split(const ProdVect& v, const ProdVect& inter) {
	ProdVect comp = complement(v, inter);
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
			if (pv.storesInfo()) {
				ret.push_back(pv);
			}
		}
		if (!iter.hasNext()) {
			break;
		}
		iter.makeNext();
	}
	if (!is_splitting(v, ret, inter)) {
		cout << "!is_splitting(v, ret)" << endl;
		cout << "v: " << v.show() << endl;
		cout << "inter: " << inter.show() << endl;
		cout << "splitting: " << endl;
		for (const auto& p : ret) {
			cout << "\t" << p.show() << endl;
		}
		exit(1);
	}
	if (ret.size() > 32) {
		cout << "splitting size: " << ret.size() << endl;
	}
	return ret;
}

struct SubstTree {
	Subst     sub;
	LightTree tree;
	string show() const;
	bool operator == (const SubstTree& st) const {
		return sub == st.sub && tree == st.tree;
	}
	bool operator != (const SubstTree& st) const {
		return !operator == (st);
	}
};

extern bool debug_union_vect;

inline string show(const vector<SubstTree>& vst) {
	string ret;
	ret += "<\n";
	for (const auto& st : vst) {
		ret += Indent::paragraph(st.show());
	}
	ret += ">/n";
	return ret;
}

inline string show(const SubstTree& st) {
	return st.show();
}

template<class Data>
struct UnionVect {
	UnionVect(bool f = false) : full_(f) { }

	bool full() const { return full_; }

	struct Pair {
		Pair(const ProdVect& k, const Data& v = Data()) : key(k), value(v), erased(false) { }
		Pair(const Pair&) = default;
		Pair& operator = (const Pair&) = default;
		ProdVect key;
		Data     value;
		bool     erased;
		string show() const {
			ostringstream oss;
			oss << key.show() << " --> " << prover::show(value);
			return oss.str();
		}
	};
	string show() const {
		if (un_.empty()) {
			return "{ }";
		}
		ostringstream oss;
		oss << "{" << endl;
		for (const auto& s : un_) {
			oss << "\t" << s.show() << endl;
		}
		oss << "}" << endl;
		return oss.str();
	}
	bool empty() const {
		return un_.empty();
	}

	bool check_uniqueness() const {
		for (auto pi = un_.begin(); pi != un_.end(); ++pi) {
			for (auto qi = un_.begin(); qi != un_.end(); ++qi) {
				if (pi != qi && pi->key == qi->key) {
					cout << "duplicate key: " << pi->key.show() << endl;
					return false;
				}
			}
		}
		return true;
	}

	void intersect(const ProdVect& pv, auto finalizer, bool may_add) {
		stack<ProdVect> to_add;
		to_add.emplace(pv);
		uint c = 0;
 		while (!to_add.empty()) {
			ProdVect q = to_add.top(); to_add.pop();
			bool intersects = false;
			for (uint i : neighbourhood(q)) {
				++c;
				Pair& p = un_[i];
				if (!p.erased && p.key.intersects_with(q)) {
					ProdVect inter = prover::intersect(p.key, q);
					intersects = true;
					if (inter != p.key) {
						p.erased = true;
						for (const auto& part : split(p.key, inter)) {
							add(part, p.value);
						}
						add(inter, p.value);
						finalizer(un_.back().value);
					} else {
						finalizer(p.value);
					}
					if (inter != q) {
						for (const auto& part : split(q, inter)) {
							to_add.emplace(part);
						}
					}
				}
			}
			if (!intersects && may_add) {
				add(q);
				finalizer(un_.back().value);
			}
		}
 		if (un_.size() > 256 && c > 8) {
 			cout << "UN SIZE:" << un_.size() << " REAL COUNT: " << c << endl;
 		}
	}

	const vector<Pair>& un() const { return un_; }

	set<uint> neighbourhood(const ProdVect& v) const {
		set<uint> ret;
		if (!maps_.size()) {
			return ret;
		}
		vector<set<uint>> sets;
		for (uint i = 0; i < v.vect.size(); ++i) {
			set<uint> inds;
			for (uint k : v.vect[i].set()) {
				if (maps_[i].count(k)) {
					for (uint j : maps_[i].at(k)) {
						inds.insert(j);
					}
				}
			}
			if (i == 0) {
				ret = inds;
			} else {
				ret = prover::intersect(ret, inds);
			}
		}
		return ret;
	}

	void add(const ProdVect& key, const Data& value = Data()) {
		if (!maps_.size()) {
			maps_ = vector<std::map<uint, vector<uint>>>(key.vect.size());
		}
		uint ind = un_.size();
		un_.emplace_back(key, value);
		for (uint i = 0; i < key.vect.size(); ++ i) {
			const Set& s = key.vect[i];
			for (uint k : s.set()) {
				maps_[i][k].push_back(ind);
			}
		}
		//if (!check_uniqueness()) {
		//	cout << "!check_uniqueness()" << endl;
		//}
	}

private:
	vector<Pair> un_;
	vector<std::map<uint, vector<uint>>> maps_;
	bool full_;
};

UnionVect<vector<SubstTree>> intersect(const UnionVect<vector<SubstTree>>& v, const UnionVect<SubstTree>& uv);

typedef map<vector<uint>, Subst> MultyUnifiedSubs;

}}}

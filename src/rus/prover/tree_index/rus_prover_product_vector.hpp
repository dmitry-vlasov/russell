#pragma once

#include "../rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover { namespace tree_index {

extern bool debug_multy_index;
extern uint matrix_vector_counter;

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
	bool operator < (const Set& s) const {
		if ((!init_ && s.init_) || (set_.size() < s.set_.size())) {
			return true;
		} else if ((init_ && !s.init_) || (set_.size() > s.set_.size())) {
			return false;
		} else {
			auto i1 = set_.begin();
			auto i2 = s.set_.begin();
			for (uint i = 0; i < set_.size(); ++i, ++i1, ++i2) {
				if (*i1 < *i2) {
					return true;
				} else if (*i1 > *i2) {
					return false;
				}
			}
			assert(operator==(s));
			return false;
		}
	}

	bool init(const TreeIndex::Leaf& ind_leafs, const vector<uint>* ind_values) {
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
	friend Set prover::tree_index::intersect(const Set& s1, const Set& s2);
	friend Set prover::tree_index::complement(const Set& s1, const Set& s2);

	std::set<uint> set_;
	bool init_;
	const TreeIndex::Leaf* index_leafs;
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
	bool operator < (const ProdVect& v) const {
		for (uint i = 0; i < vect.size(); ++ i) {
			if (vect[i] < v.vect[i]) {
				return true;
			} else if (v.vect[i] < vect[i]) {
				return false;
			}
		}
		assert(operator ==(v));
		return false;
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
			vect[i] = tree_index::intersect(vect[i], v.vect[i]);
		}
	}

	void complement(const ProdVect& v) {
		if (vect.size() != v.vect.size()) {
			cout << "vect.size() != v.vect.size(): " << vect.size() << " !=  " << v.vect.size() << endl;
		}
		assert(vect.size() == v.vect.size() && "intersect: vect.size() != v.vect.size()");
		for (uint i = 0; i < vect.size(); ++ i) {
			vect[i] = tree_index::complement(vect[i], v.vect[i]);
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

	bool contains(const vector<uint>& v) const {
		if (v.size() != vect.size()) {
			throw Error("wrong dim");
		}
		for (uint i = 0; i < v.size(); ++ i) {
			const auto& s = vect[i];
			if (s.set().find(v[i]) == s.set().end()) {
				return false;
			}
		}
		return true;
	}

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
	/*if (!is_splitting(v, ret, inter)) {
		cout << "!is_splitting(v, ret)" << endl;
		cout << "v: " << v.show() << endl;
		cout << "inter: " << inter.show() << endl;
		cout << "splitting: " << endl;
		for (const auto& p : ret) {
			cout << "\t" << p.show() << endl;
		}
		exit(1);
	}*/
	if (ret.size() > 32) {
		cout << "splitting size: " << ret.size() << endl;
	}
	return ret;
}

extern bool debug_intersect_1;

struct SubstTree {
	SubstTree() : subs_(1), trees_(1) { }
	SubstTree(const SubstTree& st) {
		for (uint i = 0; i < st.size(); ++ i) {
			subs_.push_back(st.sub(i));
			trees_.push_back(st.tree(i));
		}
	}

	SubstTree makeInc() const {
		SubstTree ret(*this);
		ret.trees_.emplace_back();
		ret.subs_.emplace_back();
		return ret;
	}

	void inc() {
		trees_.emplace_back();
		subs_.emplace_back();
	}

	LightTree& tree(uint i = -1) { return i == -1 ? trees_.back() : trees_[i]; }
	const LightTree& tree(uint i = -1) const { return i == -1 ? trees_.back() : trees_[i]; }
	Subst& sub(uint i = -1) { return i == -1 ? subs_.back() : subs_[i]; }
	const Subst& sub(uint i = -1) const { return i == -1 ? subs_.back() : subs_[i]; }

	string show(bool full = false) const {
		string ret;
		if (full) {
			for (uint i = 0; i < size(); ++ i) {
				ret += to_string(i) + " - expr: " + prover::show(tree(i)) + "\n";
				ret += Indent::paragraph(prover::show(sub(i))) + "\n";
			}
		} else {
			ret += "expr: " + prover::show(tree()) + "\n";
			ret += Indent::paragraph(prover::show(sub())) + "\n";
		}
		return ret;
	}
	bool operator == (const SubstTree& st) const {
		return subs_ == st.subs_ && trees_ == st.trees_;
	}
	bool operator != (const SubstTree& st) const {
		return !operator == (st);
	}
	uint size() const {
		return subs_.size();
	}

private:
	vector<Subst> subs_;
	vector<LightTree> trees_;
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

inline string show(const SubstTree& st, bool full = false) {
	return st.show(full);
}

inline vector<unique_ptr<SubstTree>> moveStack(vector<unique_ptr<SubstTree>>& stack) {
	vector<unique_ptr<SubstTree>> ret;
	for (auto& st : stack) {
		ret.emplace_back(st.release());
	}
	return ret;
}
inline vector<unique_ptr<SubstTree>> copyStack(const vector<unique_ptr<SubstTree>>& stack) {
	vector<unique_ptr<SubstTree>> ret;
	for (const auto& st : stack) {
		ret.emplace_back(new SubstTree(*st.get()));
	}
	return ret;
}

struct UnionVect {
	UnionVect(bool f = false) : full_(f) { }
	UnionVect(const UnionVect&) = default;
	UnionVect(UnionVect&&) = default;
	UnionVect& operator = (UnionVect&&) = default;

	bool full() const { return full_; }

	struct Value {
		enum Status {
			ACTIVE, SHADOWED, ERASED
		};
		Value(vector<unique_ptr<SubstTree>> v, Status s = ACTIVE) : stack(std::move(v)), status(s) { }
		/*Value(const vector<unique_ptr<SubstTree>>& v, Status s = ACTIVE) : stack(v), status(s) {
			for (const auto& st : v) {
				stack.emplace_back(new SubstTree(*st.get()));
			}
		}*/
		Value(Value&&) = default;
		Value(const Value& v) : status(v.status) {
			for (auto& st : v.stack) {
				stack.emplace_back(new SubstTree(*st));
			}
		}

		Value& operator = (const Value&) = default;

		vector<unique_ptr<SubstTree>> stack;
		Status status;
		bool active() const { return status == ACTIVE; }
		bool erased() const { return status == ERASED; }
		void erase() { status = ERASED; }
		void activate() { status = ACTIVE; }

		vector<unique_ptr<SubstTree>> moveStack() { return tree_index::moveStack(stack); }
		vector<unique_ptr<SubstTree>> copyStack() const { return tree_index::copyStack(stack); }

		string show() const {
			ostringstream oss;
			uint c = 0;
			for (const auto& st : stack) {
				oss << "stack level: " << c++ << endl;
				oss << st->show(true);
			}
			return oss.str();
		}
	};

	struct Pair {
		Pair(const ProdVect& k, vector<unique_ptr<SubstTree>> v, Value::Status s = Value::ACTIVE) :
		key(k), value(std::move(v)) {
			value.status = s;
		}
		//Pair(const ProdVect& k, const vector<unique_ptr<SubstTree>>& v, Value::Status s = Value::ACTIVE) :
		//key(k), value(v, s) { }
		Pair(const Pair&) = default;
		Pair& operator = (const Pair&) = default;
		ProdVect key;
		Value value;

		bool operator ==(const Pair& p) const { return key == p.key; }
		bool operator !=(const Pair& p) const { return key != p.key; }
		bool operator < (const Pair& p) const { return key < p.key; }

		string show() const {
			ostringstream oss;
			oss << showKey() << " --> " << endl;
			oss << value.show();
			return oss.str();
		}
		string showKey() const {
			ostringstream oss;
			switch (value.status) {
			case Value::ACTIVE:   oss << "ACTIVE ";   break;
			case Value::SHADOWED: oss << "SHADOWED "; break;
			case Value::ERASED:   oss <<"ERASED ";    break;
			}
			oss << key.show();
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
			oss << "\t" << s->show() << endl;
		}
		oss << "}" << endl;
		return oss.str();
	}
	string showKeys() const {
		if (un_.empty()) {
			return "{ }";
		}
		ostringstream oss;
		oss << "{" << endl;
		for (const auto& s : un_) {
			oss << "\t" << s->showKey() << endl;
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
				if (pi != qi && (*pi)->key == (*qi)->key) {
					cout << "duplicate key: " << (*pi)->key.show() << endl;
					return false;
				}
			}
		}
		return true;
	}

	void intersect(const ProdVect& pv, auto finalizer, bool may_add) {
		set<uint> n = neighbourhood(pv);
		vector<Pair> intersected_pairs;
		set<ProdVect> new_keys;
		new_keys.insert(pv);

		if (n.size() > 1000) {
			cout << "n.size() = " << n.size() << endl;
		}

		for (uint i : n) {
			Pair& p = *un_[i];
			if (!p.value.erased() && p.key.intersects_with(pv)) {
				ProdVect inter = tree_index::intersect(p.key, pv);
				if (inter != p.key) {
					bool active = p.value.active();
					p.value.erase();
					vector<unique_ptr<SubstTree>> value = p.value.moveStack();
					for (const auto& non_intersected : split(p.key, inter)) {
						add(non_intersected, std::move(copyStack(value)), active ? Value::ACTIVE : Value::SHADOWED);
					}
					intersected_pairs.emplace_back(inter, std::move(value));
					if (may_add) {
						set<ProdVect> new_new_keys;
						for (const ProdVect& q: new_keys) {
							if (q.intersects_with(inter)) {
								for (const auto& intersected : split(q, inter)) {
									new_new_keys.emplace(intersected);
								}
							} else {
								new_new_keys.emplace(q);
							}
						}
						new_keys = std::move(new_new_keys);
						if (new_keys.size() > 1000) {
							cout << "new_keys.size() = " << new_keys.size() << endl;
						}
					}
				} else {
					p.value.activate();
					finalizer(*p.value.stack.back());
				}
			}
		}
		for (auto& p : intersected_pairs) {
			add(p.key, p.value.moveStack());
			finalizer(*un_.back()->value.stack.back());
		}
		if (may_add) {
			for (const auto& k : new_keys) {
				if (find(k) == -1) {
					vector<unique_ptr<SubstTree>> v; v.emplace_back(new SubstTree());
					add(k, std::move(v));
					finalizer(*un_.back()->value.stack.back());
				}
			}
		}
	}


/*
	void intersect(const ProdVect& pv, auto finalizer, bool may_add) {
		stack<ProdVect> to_add;
		to_add.emplace(pv);
		set<ProdVect> added;
		while (!to_add.empty()) {
			ProdVect q = to_add.top();
			to_add.pop();
			if (added.count(q)) {
				continue;
			}
			added.insert(q);
			bool intersects = false;
			set<uint> n = neighbourhood(q);
			for (uint i : n) {
				Pair& p = un_[i];
				if (!p.value.erased() && p.key.intersects_with(q)) {
					ProdVect inter = prover::intersect(p.key, q);
					intersects = true;
					if (inter != p.key) {
						bool active = p.value.active();
						p.value.erase();
						stack<SubstTree> value = p.value.stack;
						for (const auto& part : split(p.key, inter)) {
							add(part, value, active ? Value::ACTIVE : Value ::SHADOWED);
						}
						add(inter, value);
						finalizer(un_.back().value.stack.top());
					} else {
						p.value.activate();
						finalizer(p.value.stack.top());
					}
					if (inter != q && may_add) {
						for (const auto& part : split(q, inter)) {
							to_add.emplace(part);
						}
					}
				}
			}
			if (may_add && !intersects) {
				stack<SubstTree> v; v.emplace();
				add(q, v);
				finalizer(un_.back().value.stack.top());
			}
		}
	}
*/
	const vector<unique_ptr<Pair>>& un() const { return un_; }

	set<uint> neighbourhood(const ProdVect& v) const;

	/*void add(const ProdVect& key, const vector<SubstTree>& value, Value::Status status = Value::ACTIVE) {
		if (!maps_.size()) {
			maps_ = vector<std::map<uint, vector<uint>>>(key.vect.size());
		}
		uint ind = un_.size();
		un_.emplace_back(new Pair(key, value, status));
		for (uint i = 0; i < key.vect.size(); ++ i) {
			const Set& s = key.vect[i];
			for (uint k : s.set()) {
				maps_[i][k].push_back(ind);
			}
		}
		if (keys_.count(key)) {
			cout << "!CHECK check_uniqueness() of key: " << key.show() << endl;
			//cout << "prev value: " << get(key)->show() << endl;
			//cout << "new  value: " << Value(value, status).show() << endl;
			exit(1);
		}
		keys_[key] = ind;
	}*/

	void add(const ProdVect& key, vector<unique_ptr<SubstTree>> value, Value::Status status = Value::ACTIVE) {
		if (!maps_.size()) {
			maps_ = vector<std::map<uint, vector<uint>>>(key.vect.size());
		}
		uint ind = un_.size();
		un_.emplace_back(new Pair(key, std::move(value), status));
		for (uint i = 0; i < key.vect.size(); ++ i) {
			const Set& s = key.vect[i];
			for (uint k : s.set()) {
				maps_[i][k].push_back(ind);
			}
		}
		if (keys_.count(key)) {
			cout << "!CHECK check_uniqueness() of key: " << key.show() << endl;
			//cout << "prev value: " << get(key)->show() << endl;
			//cout << "new  value: " << Value(value, status).show() << endl;
			exit(1);
		}
		keys_[key] = ind;
	}

	bool contains(const vector<uint>& v) const {
		for (const auto& p : un_) {
			if (p->key.contains(v)) {
				return true;
			}
		}
		return false;
	}
	uint find(const ProdVect& v) const {
		if (keys_.count(v)) {
			return keys_.at(v);
		} else {
			return -1;
		}
	}
	const Pair* get(const ProdVect& v) const {
		if (keys_.count(v)) {
			return un_[keys_.at(v)].get();
		} else {
			return nullptr;
		}
	}

private:
	vector<unique_ptr<Pair>> un_;
	vector<std::map<uint, vector<uint>>> maps_;
	map<ProdVect, uint> keys_;
	bool full_;
};

UnionVect intersect(const UnionVect& v, const UnionVect& uv);

}}}}

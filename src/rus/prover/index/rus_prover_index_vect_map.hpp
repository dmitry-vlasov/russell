#pragma once

#include "std.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

template<class T>
struct VectMap {

	VectMap(uint d) : dim_(d) { }

	uint size() const { return root.size(); }
	T& operator[] (const vector<uint>& key) { return access(key, root, 0); }
	const T& at(const vector<uint>& key) const { return const_access(key, root, 0); }

	struct Iter;
	struct ConstIter;

private:
	struct Node {
		Node() = default;
		Node(const T& v) : val_(v) { }
		uint size() const {
			uint s = has_val ? 1 : 0;
			for (const auto& p : map_) {
				s += p.second.map_->size();
			}
			return s;
		}
		bool has_val = false;
		T val_;
		map<uint, unique_ptr<Node>> map_;
	};

	typedef map<uint, unique_ptr<Node>> Map_;

	T& access(const vector<uint>& key, Node& n, uint i) {
		if (i == key.size()) {
			n.has_val = true;
			return n.val_;
		} else {
			return access(key, *n.map_[key[i]], i + 1);
		}
	}
	const T& const_access(const vector<uint>& key, Node& n, uint i) const {
		if (i == key.size()) {
			return n.val_;
		} else {
			return const_access(key, *n.map_.at(key[i]), i + 1);
		}
	}

	uint dim_;
	Node root;
};

template<class T>
struct VectMap<T>::Iter {
	Iter(uint d, bool v = true) : valid_(v), dim_(d), iters(d) { }
	Iter inc() const {
		int i = dim_ - 1;
		while (iters[i].isEnd() && i >= 0) {
			--i;
		}
		if (i == -1) {
			return Iter(dim_, false);
		} else {
			Iter ret(dim_);
			for (uint j = 0; j <= i; ++ j) {
				ret.iters[j] = iters[j];
			}
			ret.iters[i]++;
			for (j = i + 1; j < dim_; ++ j) {
				ret.iters[j].iter = ret.iters[j - 1]->second.map_.begin();
				ret.iters[j].end = ret.iters[j - 1]->second.map_.end();
			}
			return ret;
		}
	}

private:
	bool valid_;
	uint dim_;
	struct NodeIter {
		NodeIter(Map_::iterator i, Map_::iterator e) : iter(i), end(e) { }
		NodeIter& operator = () = default;
		bool isEnd() const { return iter == end; }
		void operator++() { iter++; }
		Map_::iterator iter;
		Map_::iterator end;
	};
	vector<NodeIter> iters;
};

}}}}

#pragma once

#include "../rus_prover_multy_subst.hpp"
#include "../rus_prover_subst.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

struct Index {
	struct Node {
		struct NodeIterLess {
			bool operator () (map<RuleVar, Node>::const_iterator i1, map<RuleVar, Node>::const_iterator i2) const {
				return &*i1 < &*i2;
			}
		};
		map<RuleVar, Node>::iterator parent;
		vector<uint> inds;
		map<RuleVar, Node> nodes;
		set<map<RuleVar, Node>::const_iterator, NodeIterLess> ends;
	};
	typedef map<RuleVar, Node>::iterator Iterator;
	typedef map<RuleVar, Node>::const_iterator ConstIterator;
	typedef map<uint, Subst> Unified;
	struct Iter;

	void add(const Term& t, uint val = -1);
	Unified unify(const Term&) const;
	vector<pair<Term, uint>> unpack() const;
	string show() const;
	string show_pointers() const;

	static vector<pair<Term, uint>> unpack(const Node&);
	static string show(const Node&);
	static string show_pointers(const Node&);

	uint totalNodes() const;
	bool empty() const { return root.nodes.empty(); }

	uint size = 0;
	Node root;
};

struct Index::Iter {
	Iter() : valid_(false) { }
	Iter(const Node& n) : valid_(true), beg_(n.nodes.begin()), iter_(n.nodes.begin()), end_(n.nodes.end()) { }
	Iter(ConstIterator i) : valid_(i != ConstIterator()), iter_(i) { }
	Iter(ConstIterator b, ConstIterator e, bool v = true) : valid_(v && b != ConstIterator()), beg_(b), iter_(b), end_(e) { }
	Iter(const Iter&) = default;
	Iter& operator = (const Iter&) = default;
	bool operator == (const Iter& i) const {
		return &*iter_ == &*i.iter_;
	}
	bool operator != (const Iter& i) const {
		return &*iter_ != &*i.iter_;
	}
	Iter side() const {
		if (!valid_ || isSideEnd()) {
			return Iter(beg_, iter_, end_, false);
		} else {
			auto i = iter_;
			return Iter(beg_, ++i, end_);
		}
	}
	Iter next() const {
		if (!valid_ || isNextEnd()) {
			return Iter(beg_, iter_, end_, false);
		} else {
			return Iter(iter_->second.nodes.begin(), iter_->second.nodes.end());
		}
	}
	Iter prev() const {
		return Iter(iter_->second.parent);
	}
	Iter reset() const {
		return Iter(beg_, end_, valid_);
	}
	bool isNextEnd() const { return iter_->second.nodes.size() == 0; }
	bool isSideEnd() const {
		if (end_ == ConstIterator()) {
			return true;
		} else {
			auto i = iter_; return ++i == end_;
		}
	}
	bool isValid() const { return valid_; }
	ConstIterator iter() const {
		if (!valid_) {
			throw Error("Not valid Index::Iter");
		}
		return iter_;
	}
	Term subTerm(ConstIterator) const;
	Term subTerm(const Iter& i) const {
		return subTerm(i.iter_);
	}

	vector<pair<Term, Iter>> subTerms() const {
		vector<pair<Term, Iter>> ret;
		ret.reserve(iter_->second.ends.size());
		for (auto end : iter_->second.ends) {
			ret.emplace_back(subTerm(end), Iter(end));
		}
		return ret;
	}
	vector<Iter> ends() const {
		vector<Iter> ret;
		ret.reserve(iter_->second.ends.size());
		for (auto end : iter_->second.ends) {
			ret.emplace_back(end);
		}
		return ret;
	}
	bool isEnd(const Iter& i) const {
		return iter_->second.ends.find(i.iter()) != iter_->second.ends.end();
	}
	bool isVar() const {
		return iter_->first.isVar() && iter_->first.var.rep;
	}
	LightSymbol var() const {
		return iter_->first.var;
	}
	RuleVar ruleVar() const {
		return iter_->first;
	}
	string show(bool full = false) const {
		ostringstream oss;
			if (full) {
			oss << "iter: " << ((iter_ == ConstIterator()) ? "<>" : iter_->first.show()) << "\n";
			oss << "inds: ";
			for (uint i : iter_->second.inds) {
				oss << to_string(i) << " ";
			}
			oss << "\n";
		} else {
			oss << ((iter_ == ConstIterator()) ? "<>" : iter_->first.show()) << "=(" << (void*)&*iter_ << ") " ;
			if (iter_->second.inds.size()) {
				oss << "[";
				for (uint i : iter_->second.inds) {
					oss << to_string(i) + " ";
				}
				oss << "]";
			}
		}
		return oss.str();
	}
	string showBranch() const {
		vector<Iter> branch;
		Iter i = *this;
		while (i.isValid()) {
			branch.push_back(i);
			i = i.prev();
		}
		std::reverse(branch.begin(), branch.end());
		string ret;
		for (auto it : branch) {
			ret += it.show();
		}
		return ret;
	}

private:
	Iter(ConstIterator b, ConstIterator i, ConstIterator e, bool v = true) :
		valid_(v), beg_(b), iter_(i), end_(e) { }
	bool valid_;
	ConstIterator beg_;
	ConstIterator iter_;
	ConstIterator end_;
};

template<class Data>
struct IndexMap {
	struct Unified {
		Unified(const Data& d, Subst&& s) : data(d), sub(std::move(s)) { }
		Data data;
		Subst sub;
	};
	void add(const Term& t, const Data& d) {
		index_.add(t);
		data_.push_back(d);
	}
	string show() const {
		vector<pair<Term, uint>> terms = index_.unpack();
		if (!terms.size()) {
			return "\n";
		} else {
			string ret;
			for (const auto&  p : terms) {
				Data d = data_[p.second];
				ret += "[" + p.first.show() + "]" + " -> " + to_string(p.second) + "\n";
			}
			return ret;
		}
	}
	string show_pointers() const {
		return index_.show_pointers();
	}
	const Index& index() const { return index_; }
	const vector<Data>& data() const { return data_; }

private:
	Index index_;
	vector<Data> data_;
};

template<class D>
inline vector<typename IndexMap<D>::Unified> unify(const IndexMap<D>& m, const Term& t) {
	vector<typename IndexMap<D>::Unified> ret;
	Index::Unified unif = m.index().unify(t);
	for (auto& p : unif) {
		if (p.second.ok()) {
			ret.emplace_back(m.data().at(p.first), p.second);
		}
	}
	return ret;
}

}}}}

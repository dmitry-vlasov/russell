#pragma once

#include "../rus_prover_multy_subst.hpp"
#include "../rus_prover_subst.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

struct Index {
	struct Node {
		struct NodeIterLess {
			bool operator () (map<RuleVar, Node>::const_iterator i1, map<RuleVar, Node>::const_iterator i2) const {
				return &*i1 < &*i2;
			}
		};
		map<RuleVar, Node>::iterator parent;
		vector<uint> inds1;
		vector<uint> vals;
		map<RuleVar, Node> nodes;

		set<map<RuleVar, Node>::const_iterator, NodeIterLess> ends; // All ends of terms, which start at current node
		set<map<RuleVar, Node>::const_iterator, NodeIterLess> vars; // All variables among nodes
		set<uint> lens;
	};
	typedef map<RuleVar, Node>::iterator Iterator;
	typedef map<RuleVar, Node>::const_iterator ConstIterator;
	typedef map<uint, Subst> Unified;
	typedef vector<pair<Term, vector<uint>>> Unpacked;
	struct Iter;

	void add(const Term& t, uint val = -1);
	Unpacked unpack() const;
	string show() const;
	string show_pointers() const;

	static Unpacked unpack(const Node&);
	static Unpacked unpack(Iter);
	static string show(const Node&);
	static string show(Iter);
	static string show_pointers(const Node&);

	uint totalNodes() const;
	bool empty() const { return root_.nodes.empty(); }
	void verify(bool show = false) const;

	uint size() const { return size_; }
	const Node& root() const {
		if (!endsInitialized) {
			const_cast<Index*>(this)->initEnds();
		}
		return root_;
	}

private:
	void initEnds();
	uint size_ = 0;
	Node root_;
	bool endsInitialized = false;
	vector<Term> terms;
};

struct Index::Iter {
	Iter() : valid_(false), map_(nullptr) { }
	Iter(const Node& n) : valid_(true), beg_(n.nodes.begin()), iter_(n.nodes.begin()), end_(n.nodes.end()), map_(&n.nodes) { }
	Iter(const map<RuleVar, Node>* m, ConstIterator i) : valid_(i != ConstIterator()), iter_(i), map_(m) { }
	Iter(const map<RuleVar, Node>* m, ConstIterator b, ConstIterator e, bool v = true) : valid_(v && b != ConstIterator()), beg_(b), iter_(b), end_(e), map_(m) { }
	Iter(const Iter&) = default;
	Iter& operator = (const Iter&) = default;
	bool operator == (const Iter& i) const {
		return iter_ == i.iter_;
	}
	bool operator != (const Iter& i) const {
		return !operator ==(i);
	}
	void setHint(const Rule* r) {
		hint_ = r;
	}
	Iter side() const {
		if (hint_) {
			Iter i(*this);
			while (true) {
				i = i.elementarySide();
				if (!i.isValid() || i.isVar() || i.ruleVar().rule == hint_) {
					break;
				}
			}
			return i;
		} else {
			return elementarySide();
		}
	}
	Iter next() const {
		if (!valid_ || isNextEnd()) {
			return Iter(map_, beg_, iter_, end_, false);
		} else {
			return Iter(&iter_->second.nodes, iter_->second.nodes.begin(), iter_->second.nodes.end());
		}
	}
	Iter prev() const {
		return Iter(nullptr, iter_->second.parent, ConstIterator());
	}
	Iter reset() const {
		return Iter(map_, beg_, beg_, end_, valid_);
	}
	bool isNextEnd() const {
		return iter_->second.nodes.size() == 0;
	}
	bool isSideEnd() const {
		return !side().isValid();
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
			ret.emplace_back(subTerm(end), Iter(&iter_->second.nodes, end));
		}
		return ret;
	}
	vector<Iter> ends() const {
		vector<Iter> ret;
		ret.reserve(iter_->second.ends.size());
		for (auto end : iter_->second.ends) {
			ret.emplace_back(&iter_->second.nodes, end);
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
	const Node& node() const {
		return iter_->second;
	}
	string show(bool full = false) const {
		ostringstream oss;
			if (full) {
			oss << "iter: " << ((iter_ == ConstIterator()) ? "<>" : iter_->first.show()) << " =(" << (void*)&*iter_ << ") " << "\n";
			if (iter_->second.ends.size()) {
				oss << "ends: ";
				for (auto i : iter_->second.ends) {
					oss << (void*)&*i << " ";
				}
				oss << "\n";
			}
			if (iter_->second.vals.size()) {
				oss << "vals: ";
				for (uint i : iter_->second.vals) {
					oss << to_string(i) << " ";
				}
				oss << "\n";
			}
			if (iter_->second.inds1.size()) {
				oss << "inds: ";
				for (uint i : iter_->second.inds1) {
					oss << to_string(i) << " ";
				}
				oss << "\n";
			}
			oss << "\n";
		} else {
			oss << ((iter_ == ConstIterator()) ? "<>" : iter_->first.show()) << "=(" << (void*)&*iter_ << ") " ;
			if (iter_->second.vals.size()) {
				oss << "[";
				for (uint i : iter_->second.vals) {
					oss << to_string(i) + " ";
				}
				oss << "]";
			}
		}
		return oss.str();
	}
	string showBranch(bool full = false) const {
		vector<Iter> branch;
		Iter i = *this;
		while (i.isValid()) {
			branch.push_back(i);
			i = i.prev();
		}
		std::reverse(branch.begin(), branch.end());
		string ret;
		for (auto it : branch) {
			ret += it.show(full);
		}
		return ret;
	}
	string showTree() const {
		return Index::show(*this);
	}

private:
	bool isElementarySideEnd() const {
		if (end_ == ConstIterator()) {
			return true;
		} else {
			auto i = iter_;
			return ++i == end_;
		}
	}
	Iter elementarySide() const {
		if (!valid_ || isElementarySideEnd()) {
			return Iter(map_, beg_, iter_, end_, false);
		} else {
			auto i = iter_;
			return Iter(map_, beg_, ++i, end_, true);
		}
	}
	Iter(const map<RuleVar, Node>* m, ConstIterator b, ConstIterator i, ConstIterator e, bool v) :
		valid_(v), beg_(b), iter_(i), end_(e), map_(m) { }
	bool valid_;
	ConstIterator beg_;
	ConstIterator iter_;
	ConstIterator end_;
	const map<RuleVar, Node>* map_;
	const Rule* hint_ = nullptr;
};

template<class Data>
struct IndexMap {
	struct Unified {
		Unified(const Data& d, Subst&& s) : data(d), sub(std::move(s)) { }
		Unified(const Unified&) = default;
		Unified(Unified&&) = default;
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

}}}}

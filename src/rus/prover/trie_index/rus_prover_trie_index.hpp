#pragma once

#include "rus_prover_trie_flat_subst.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct TrieIndex {
	struct Node {
		struct NodeIterLess {
			bool operator () (map<RuleVar, Node>::iterator i1, map<RuleVar, Node>::iterator i2) const {
				return &*i1 < &*i2;
			}
		};
		map<RuleVar, Node>::iterator parent;
		vector<uint> inds;
		map<RuleVar, Node> nodes;
		set<map<RuleVar, Node>::iterator, NodeIterLess> ends;
	};
	typedef map<RuleVar, Node>::iterator Iterator;
	typedef map<RuleVar, Node>::const_iterator ConstIterator;

	struct TrieIter {
		TrieIter() : valid_(false) { }
		TrieIter(const Node& n) :
			valid_(true), beg_(n.nodes.begin()), iter_(n.nodes.begin()), end_(n.nodes.end()) { }
		TrieIter(ConstIterator i) :
			valid_(i != ConstIterator()), iter_(i) { }
		TrieIter(ConstIterator b, ConstIterator e, bool v = true) :
			valid_(v && b != ConstIterator()), beg_(b), iter_(b), end_(e) { }
		TrieIter(const TrieIter&) = default;
		TrieIter& operator = (const TrieIter&) = default;
		TrieIter side() const {
			if (!valid_ || isSideEnd()) {
				return TrieIter(beg_, iter_, end_, false);
			} else {
				auto i = iter_;
				return TrieIter(beg_, ++i, end_);
			}
		}
		TrieIter next() const {
			if (!valid_ || isNextEnd()) {
				return TrieIter(beg_, iter_, end_, false);
			} else {
				return TrieIter(iter_->second.nodes.begin(), iter_->second.nodes.end());
			}
		}
		TrieIter prev() const {
			return TrieIter(iter_->second.parent);
		}
		TrieIter reset() const {
			return TrieIter(beg_, end_, valid_);
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
				cout << "NOT VALID!!!" << endl;
			}
			assert(valid_ && "TrieIter::iter()");
			return iter_;
		}
		FlatTerm subTerm(ConstIterator) const;

		vector<pair<FlatTerm, TrieIter>> subTerms() const {
			vector<pair<FlatTerm, TrieIter>> ret;
			ret.reserve(iter_->second.ends.size());
			for (auto end : iter_->second.ends) {
				ret.emplace_back(subTerm(end), TrieIter(end));
			}
			return ret;
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
			string ret;
				if (full) {
				//ret += "beg: " + ((beg_ == ConstIterator()) ? "<>" : beg_->first.show()) + "\n";
				ret += "iter: " + ((iter_ == ConstIterator()) ? "<>" : iter_->first.show()) + "\n";
				//ret += "end: " + ((end_ == ConstIterator()) ? "<>" : end_->first.show()) + "\n";
				ret += "inds: ";
				for (uint i : iter_->second.inds) {
					ret += to_string(i) + " ";
				}
				ret += "\n";
			} else {
				ret += ((iter_ == ConstIterator()) ? "<>" : iter_->first.show()) + " ";
				if (iter_->second.inds.size()) {
					ret += "[";
					for (uint i : iter_->second.inds) {
						ret += to_string(i) + " ";
					}
					ret += "]";
				}
			}
			return ret;
		}
		string showBranch() const {
			vector<TrieIter> branch;
			TrieIter i = *this;
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
		TrieIter(ConstIterator b, ConstIterator i, ConstIterator e, bool v = true) :
			valid_(v), beg_(b), iter_(i), end_(e) { }
		bool valid_;
		ConstIterator beg_;
		ConstIterator iter_;
		ConstIterator end_;
	};

	typedef map<uint, FlatSubst> Unified;

	void add(const FlatTerm& t);
	Unified unify(const FlatTerm&) const;
	vector<pair<FlatTerm, uint>> unpack() const;
	string show() const;
	uint totalNodes() const;

	uint size = 0;
	Node root;
};

template<class Data>
struct TrieIndexMap {
	struct Unified {
		Unified(const Data& d, Subst&& s) : data(d), sub(std::move(s)) { }
		Data  data;
		Subst sub;
	};
	void add(const LightTree& t, const Data& d) {
		//cout << "ADDING: " << prover::show(t) << " --> " << data_.size() << endl;
		index_.add(convert2flatterm(t));
		data_.push_back(d);
	}
	vector<Unified> unify(const LightTree& t) {
		vector<Unified> ret;
		TrieIndex::Unified unif = index_.unify(convert2flatterm(t));
		for (auto& p : unif) {
			if (p.second.ok) {
				//cout << "UNIFIED: " << p.first << endl;
				ret.emplace_back(data_[p.first], convert2subst(p.second));
			}
		}
		return ret;
	}
	string show() const {
		vector<pair<FlatTerm, uint>> terms = index_.unpack();
		if (!terms.size()) {
			return "\n";
		} else {
			string ret;
			for (const auto&  p : terms) {
				Data d = data_[p.second];
				ret += "[" + p.first.show() + "]" + " -> " + to_string(p.second)/*prover::show(d)*/ + "\n";
			}
			return ret;
		}
	}

	const TrieIndex& index() const { return index_; }
	const vector<Data>& data() const { return data_; }

private:
	TrieIndex index_;
	vector<Data> data_;
};

extern bool debug_trie_index;

}}}}

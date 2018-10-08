#pragma once

#include "rus_prover_trie_flat_subst.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct TrieIndex {
	struct Node {
		Node(const RuleVar& rv) : ruleVar(rv) { }
		RuleVar ruleVar;
		uint ind = -1;
		unique_ptr<Node> next;
		unique_ptr<Node> side;
		vector<Node*> ends;
	};

	typedef map<uint, FlatSubst> Unified;

	void add(const FlatTerm& t);
	Unified unify(const FlatTerm&) const;
	vector<pair<FlatTerm, uint>> unpack() const;
	string show() const;

	uint size = 0;
	unique_ptr<Node> root;
};

template<class Data>
struct TrieIndexMap {
	struct Unified {
		Unified(const Data& d, Subst&& s) : data(d), sub(std::move(s)) { }
		Data  data;
		Subst sub;
	};
	void add(const LightTree& t, const Data& d) {
		index_.add(convert2flatterm(t));
		data_.push_back(d);
	}
	vector<Unified> unify(const LightTree& t) {
		vector<Unified> ret;
		TrieIndex::Unified unif = index_.unify(convert2flatterm(t));
		for (auto& p : unif) {
			if (p.second.ok) {
				ret.emplace_back(data_[p.first], std::move(p.second));
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

}}}}

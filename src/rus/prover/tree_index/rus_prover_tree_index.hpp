#pragma once

#include "../rus_prover_unify.hpp"
#include "../rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover { namespace tree_index {

struct TreeIndex {
	struct Leaf {
		set<uint> inds;
	};
	struct Branch {
		Branch(uint a) {
			for (uint i = 0; i < a; ++ i) {
				child.push_back(make_unique<TreeIndex>());
			}
		}
		vector<unique_ptr<TreeIndex>> child;
	};
	struct Node {
		enum Kind { LEAF, BRANCH };
		Node(Leaf&& l) : node(std::move(l)) { }
		Node(Branch&& b) : node(std::move(b)) { }

		Kind kind() const { return static_cast<Kind>(node.index()); }
		Leaf& leaf() { return std::get<Leaf>(node); }
		Branch& branch() { return std::get<Branch>(node); }
		const Leaf& leaf() const { return std::get<Leaf>(node); }
		const Branch& branch() const { return std::get<Branch>(node); }

		variant<Leaf, Branch> node;
	};
	typedef map<uint, Subst> Unified;

	map<const Rule*, Node> rules;
	map<LightSymbol, Leaf> vars;
	uint size = 0;

	uint add(const LightTree&);
	Unified unify(const LightTree&) const;
	string show() const;
	map<uint, string> showVector() const;

	vector<LightTree> exprs;
};

inline string show(const vector<const TreeIndex*>& mindex) {
	string ret;
	for (uint i = 0; i < mindex.size(); ++ i) {
		ret += "index: " + to_string(i) + "\n";
		ret += mindex[i]->show() + "\n";
		ret += "-----------------------------\n\n";
	}
	return ret;
}

template<class Data>
struct TreeIndexMap {
	struct Unified {
		Unified(const Data& d, Subst&& s) : data(d), sub(std::move(s)) { }
		Data  data;
		Subst sub;
	};
	void add(const LightTree& t, const Data& d) {
		index_.add(t);
		data_.push_back(d);
	}
	vector<Unified> unify(const LightTree& t) {
		vector<Unified> ret;
		TreeIndex::Unified unif = index_.unify(t);
		for (auto& p : unif) {
			if (p.second.ok) {
				ret.emplace_back(data_[p.first], std::move(p.second));
			}
		}
		return ret;
	}
	string show() const {
		map<uint, string> lines = index_.showVector();
		if (!lines.size()) {
			return "\n";
		} else {
			string ret;
			for (const auto&  p : lines) {
				uint ind = p.first;
				Data d = data_[ind];
				//ret += to_string(d) + "[" + to_string(p.first) + "]" + " -> " + p.second + "\n";
				ret += to_string(p.first) + " -> " + p.second + "\n";
			}
			return ret;
		}
		return index_.show();
	}

	const TreeIndex& index() const { return index_; }
	const vector<Data>& data() const { return data_; }

private:
	TreeIndex index_;
	vector<Data> data_;
};

typedef TreeIndexMap<uint> IndexInt;

extern bool debug_index;
extern bool debug_ind;

}}}}


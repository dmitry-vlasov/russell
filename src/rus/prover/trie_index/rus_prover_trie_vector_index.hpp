#pragma once

#include "rus_prover_trie_unify_iter.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct CartesianCell {
	CartesianCell(const vector<uint>& ex, bool em) : extra_inds(ex), empty_index(em) {
		sort(extra_inds.begin(), extra_inds.end());
	}
	CartesianCell(const CartesianCell&) = default;
	CartesianCell(CartesianCell&&) = default;

	bool extraContains(uint i) const {
		return std::binary_search(extra_inds.begin(), extra_inds.end(), i);
	}
	bool empty() const {
		return !extra_inds.size() && empty_index;
	}
	vector<uint> extra_inds;
	bool empty_index;
};

struct VectorUnified {
	vector<uint> complete(const vector<uint>& v) const {
		vector<uint> ret(vect.size(), -1);
		for (uint i = 0, j = 0; i < vect.size(); ++ i) {
			if (!vect.at(i).empty_index) {
				ret[i] = v.at(j++);
			}
		}
		return ret;
	}
	bool empty() const {
		for (const auto& c : vect) {
			if (c.empty()) {
				return true;
			}
		}
		return !unified.size();
	}

	vector<CartesianCell> vect;
	map<vector<uint>, FlatTermSubst> unified;
};

struct VectorIndex {
	VectorIndex(uint dim) : vect(dim) { }
	struct Cell {
		void init(const vector<uint>& all_inds) {
			all_inds_ = all_inds;
			std::sort(inds_in_exprs.begin(), inds_in_exprs.end());
			for (uint i : all_inds_) {
				if (!std::binary_search(inds_in_exprs.begin(), inds_in_exprs.end(), i)) {
					extra_inds_.push_back(i);
				}
			}
		}
		void add(const LightTree& e, uint i) {
			inds_in_exprs.push_back(i);
			exprs_.add(e, i);
		}
		bool empty() const {
			return !extra_inds_.size() && exprs_.empty();
		}
		const TrieIndex& exprs() const { return exprs_; }
		const vector<uint>& extraInds() const { return extra_inds_; }
		const vector<uint>& allInds() const { return all_inds_; }

	private:
		TrieIndex    exprs_;
		vector<uint> extra_inds_;
		vector<uint> all_inds_;
		vector<uint> inds_in_exprs;
	};
	VectorUnified unify_general() {
		vector<BothIter> iters;
		VectorUnified ret;
		cout << "VectorIndex::unify_general(): STARTED" << endl;
		try {
			for (const auto& c : vect) {
				ret.vect.emplace_back(c.extraInds(), c.exprs().empty());
				if (!c.exprs().empty()) {
					iters.emplace_back(TrieIndex::TrieIter(c.exprs().root));
				}
			}
			ret.unified = trie_index::unify_general(iters);
		} catch (Error& err) {
			cerr << endl << "VectorIndex::unify_general(): ERROR" << endl;
			for (const auto& c : vect) {
				cerr << "CELL: " << endl;
				cerr << c.exprs().show_pointers() << endl << endl;
			}
			throw err;
		}
		return ret;
	}
	vector<Cell> vect;
};

}}}}

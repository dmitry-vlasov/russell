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
	string show() const {
		string ret;
		ret += (empty_index ? "(empty)" : "") + string("extra_inds: ") + prover::show(extra_inds) + "\n";
		return ret;
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

	string show() const {
		string ret;
		ret += "<VectorUnified>\n";
		ret += "cartesian cells:\n";
		for (const auto& c : vect) {
			ret += "\t" + c.show();
		}
		ret += "unified:\n";
		for (const auto& p : unified) {
			ret += "\t" + prover::show(p.first) + " --> " + p.second.show() + "\n";
		}
		return ret;
	}

	vector<CartesianCell> vect;
	map<vector<uint>, FlatTermSubst> unified;
};

struct VectorIndex {
	VectorIndex(uint dim) {
		for (uint i = 0; i < dim; ++ i) vect.emplace_back(new Cell);
	}
	struct Cell {
		Cell() = default;
		Cell(const Cell&) = delete;
		void init(const vector<uint>& all_inds) {
			all_inds_ = all_inds;
			std::sort(exprs_inds_.begin(), exprs_inds_.end());
			for (uint i : all_inds_) {
				if (!std::binary_search(exprs_inds_.begin(), exprs_inds_.end(), i)) {
					extra_inds_.push_back(i);
				}
			}
		}
		void add(const LightTree& e, uint i) {
			exprs_inds_.push_back(i);
			exprs_.add(e, i);
		}
		bool empty() const {
			return !extra_inds_.size() && exprs_.empty();
		}
		const TrieIndex& exprs() const { return exprs_; }
		const vector<uint>& extraInds() const { return extra_inds_; }
		const vector<uint>& allInds() const { return all_inds_; }
		const vector<uint>& exprsInds() const { return exprs_inds_; }
		string show() const { return exprs_.show(); }

	private:
		TrieIndex    exprs_;
		vector<uint> extra_inds_;
		vector<uint> all_inds_;
		vector<uint> exprs_inds_;
	};
	VectorUnified unify_general() {
		vector<MultyIter> iters;
		VectorUnified ret;
		try {
			for (auto& c : vect) {
				ret.vect.emplace_back(c->extraInds(), c->exprs().empty());
				if (!c->exprs().empty()) {
					iters.emplace_back(TrieIndex::TrieIter(c->exprs().root));
				}
			}
			ret.unified = trie_index::unify_general(iters);
		} catch (Error& err) {
			cout << endl << "VectorIndex::unify_general(): ERROR" << endl;
			for (auto& c : vect) {
				cout << "CELL: " << endl;
				cout << c->exprs().show_pointers() << endl << endl;
			}

			//debug_trie_index = true;
			ret.unified = trie_index::unify_general(iters);

			throw err;
		}
		return ret;
	}
	vector<unique_ptr<Cell>> vect;
};

}}}}

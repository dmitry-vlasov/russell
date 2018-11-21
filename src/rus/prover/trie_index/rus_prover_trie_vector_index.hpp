#pragma once

#include "rus_prover_trie_unify_iter.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct VectorUnified {
	struct Cell {
		Cell(const vector<uint>& ex, bool em) : extra_inds(ex), is_empty(em) {
			sort(extra_inds.begin(), extra_inds.end());
		}
		bool extraContains(uint i) const {
			return std::binary_search(extra_inds.begin(), extra_inds.end(), i);
		}
		vector<uint> extra_inds;
		bool is_empty;
	};
	vector<Cell> vect;
	GeneralUnified unified;
	vector<uint> complete(const vector<uint>& v) const {
		vector<uint> ret(vect.size(), -1);
		for (uint i = 0, j = 0; i < vect.size(); ++ i) {
			if (!vect.at(i).is_empty) {
				ret[i] = v.at(j++);
			}
		}
		return ret;
	}
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
		for (const auto& c : vect) {
			ret.vect.emplace_back(c.extraInds(), c.exprs().empty());
			if (!c.exprs().empty()) {
				iters.emplace_back(TrieIndex::TrieIter(c.exprs().root));
			}
		}
		ret.unified = trie_index::unify_general(iters);
		/*for (auto& p : unif) {
			if (p.second.sub.ok) {
				//cout << "UNIFIED: " << p.first << endl;
				ret.emplace_back(m.data().at(p.first[0]), convert2subst(p.second.sub));
			}
		}*/
		return ret;
	}
	vector<Cell> vect;
};

VectorUnified intersect(const VectorUnified& vu1, const VectorUnified& vu2);

}}}}

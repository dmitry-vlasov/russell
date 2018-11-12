#pragma once

#include "rus_prover_trie_unify_iter.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct VectorIndex {
	VectorIndex(uint dim) : vect(dim) { }
	struct Cell {
		void init(const vector<uint>& all_inds) {
			for (uint i : all_inds) {
				if (inds_in_exprs.find(i) == inds_in_exprs.end()) {
					extra_inds_.push_back(i);
				}
			}
		}
		void add(const LightTree& e, uint i) {
			inds_in_exprs.insert(i);
			exprs_.add(e, i);
		}
		const TrieIndex& exprs() const { return exprs_; }
		const vector<uint>& extraInds() const { return extra_inds_; }

	private:
		TrieIndex    exprs_;
		vector<uint> extra_inds_;
		set<uint>    inds_in_exprs;
	};
	void unify_general() {
		vector<BothIter> iters;
		for (const auto& c : vect) {
			if (!c.exprs().empty()) {
				iters.emplace_back(TrieIndex::TrieIter(c.exprs().root));
			}
		}
		unified = trie_index::unify_general(iters);
		/*for (auto& p : unif) {
			if (p.second.sub.ok) {
				//cout << "UNIFIED: " << p.first << endl;
				ret.emplace_back(m.data().at(p.first[0]), convert2subst(p.second.sub));
			}
		}*/
	}
	vector<Cell> vect;
	GeneralUnified unified;
};

}}}}

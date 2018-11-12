#pragma once

#include "rus_prover_trie_unify_iter.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct ColumnUnified {

};

struct VectorIndex {
	VectorIndex(uint dim) : vect(dim) { }
	struct Cell {
		void init(const vector<uint>& all_inds) {
			for (uint i : all_inds) {
				if (inds_in_exprs.find(i) == inds_in_exprs.end()) {
					inds_.push_back(i);
				}
			}
		}
		void add(const LightTree& e, uint i) {
			inds_in_exprs.insert(i);
			exprs_.add(e, i);
		}
		const TrieIndex& exprs() const { return exprs_; }
		const vector<uint>& inds() const { return inds_; }

	private:
		TrieIndex    exprs_;
		vector<uint> inds_;
		set<uint>    inds_in_exprs;
	};
	GeneralUnified unify_general(const VectorIndex& m) {
		GeneralUnified ret;
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
		return ret;
	}
	vector<Cell> vect;
	GeneralUnified unified;
};

struct MatrixIndex {
	MatrixIndex(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs);

	MultyUnifiedSubs compute(MultyUnifiedSubs& unif);

	string show() const;
	uint card() const;
	string card_str() const;
	uint dim_hyp() const { return dim_hyp_; }
	uint dim_vars() const { return mindex_.size(); }
	bool empty() const { return empty_; }

private:
	uint dim_hyp_;
	map<LightSymbol, VectorIndex> mindex_;
	vector<vector<uint>> proofInds_;
	bool empty_;
};

string show(const MultyUnifiedSubs&);
MultyUnifiedSubs unify_subs_matrix(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs);

extern bool debug_trie_matrix;

}}}}

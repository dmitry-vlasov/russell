#pragma once

#include "../rus_prover_node.hpp"
#include "rus_prover_trie_vector_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct MatrixUnified {
	enum Kind { FULL, EMPTY, NORM };
	MatrixUnified(Kind k = FULL) : kind(k) { }
	MatrixUnified intersect(const VectorUnified&) const;
	map<vector<uint>, vector<FlatTermSubst>> unfold() const;
	bool empty() const {
		if (kind == EMPTY) {
			return true;
		}
		for (const auto& c : vect) {
			if (c.empty()) {
				return true;
			}
		}
		return !unified.size();
	}
	string show() const {
		string ret;
		ret += "<MatrixUnified>\n";
		ret += "cartesian cells:\n";
		for (const auto& c : vect) {
			ret += "\t" + c.show();
		}
		ret += "unified:\n";
		for (const auto& p : unified) {
			ret += "\t" + prover::show(p.first) + " --> \n";
			for (const auto& t : p.second) {
				ret += "\t\t" + t.show() + "\n";
			}
		}
		return ret;
	}

	Kind kind;
	vector<CartesianCell> vect;
	map<vector<uint>, vector<FlatTermSubst>> unified;
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
	map<LightSymbol, unique_ptr<VectorIndex>> mindex_;
	vector<vector<uint>> proofInds_;
	bool empty_;
};

}}}}

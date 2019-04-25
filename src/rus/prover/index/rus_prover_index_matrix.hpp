#pragma once

#include "../rus_prover_node.hpp"
#include "../rus_prover_limit.hpp"
#include "rus_prover_index_vector.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

typedef MapUnified<vector<TermSubst>> MatrixUnified;

struct MatrixUnifiedUnion {
	enum Kind { FULL, EMPTY, NORM };
	MatrixUnifiedUnion(Kind k = FULL) : kind(k) { }
	MatrixUnifiedUnion intersect(const VectorUnifiedUnion&, uint i) const;
	MatrixUnifiedUnion intersect1(const VectorUnifiedUnion&, uint i) const;
	map<vector<uint>, vector<TermSubst>> unfold(std::function<vector<TermSubst>()> def_val) const {
		map<vector<uint>, vector<TermSubst>> ret;
		for (const auto& mu : union_) {
			for (const auto& p : mu.unfold(def_val)) {
				ret.emplace(p.first, p.second);
			}
		}
		return ret;
	}
	bool empty() const {
		if (kind == EMPTY) {
			return true;
		}
		for (const auto& m : union_) {
			if (!m.empty()) {
				return false;
			}
		}
		return true;
	}
	uint card() const {
		uint c = 0;
		for (const auto& mu : union_) {
			c += mu.card();
		}
		return c;
	}
	string show() const {
		switch (kind) {
		case FULL:  return "MatrixUnifiedUnion: Full\n";
		case EMPTY: return "MatrixUnifiedUnion: Empty\n";
		default: {
			string ret;
			ret += "MatrixUnifiedUnion: Normal\n";
			ret += "card = " + to_string(card()) + "\n";
			ret += index::show(union_);
			return ret;
		}
		}
	}

	Kind kind;
	vector<MatrixUnified> union_;
};

struct Matrix{
	Matrix(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs, const ProofsSizeLimit* limit);

	MultyUnifiedSubs compute(MultyUnifiedSubs& unif);

	string show() const;
	uint card() const;
	string card_str() const;
	uint dim_hyp() const { return dim_hyp_; }
	uint dim_vars() const { return mindex_.size(); }
	bool empty() const { return empty_; }

private:
	uint dim_hyp_;
	map<uint, unique_ptr<Vector>> mindex_;
	vector<vector<uint>> proofInds_;
	bool empty_;
};

MultyUnifiedSubs intersect(const map<uint, VectorUnifiedUnion>& terms, MultyUnifiedSubs& unif);

}}}}

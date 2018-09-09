#pragma once

#include "rus_prover_index.hpp"
#include "rus_prover_vector_unified.hpp"
#include "rus_prover_product_unified.hpp"

namespace mdl { namespace rus { namespace prover {

struct VectorIndex {
	struct IndexPtr {
		IndexPtr(const Index* i, const vector<uint>* v, const vector<uint>& pi) :
			ind(i), values(v), proofsSize(pi.size()), proofInds(pi) {
			set<uint> vals;
			for (auto val : *values) {
				vals.insert(val);
			}
			for (uint i : pi) {
				if (vals.find(i) == vals.end()) {
					obligatory.push_back(i);
				}
			}
		}
		IndexPtr(const IndexPtr&) = default;
		IndexPtr& operator = (const IndexPtr&) = default;
		const Index* ind;
		const vector<uint>* values;
		uint proofsSize;
		vector<uint> obligatory;
		vector<uint> proofInds;
	};
	uint size() const {
		return vect_.size();
	}
	void add(const IndexInt& i, const vector<uint>& pi) {
		vect_.emplace_back(&i.index(), &i.data(), pi);
	}
	void add(const Index* i, const vector<uint>* v, const vector<uint>& pi) {
		vect_.emplace_back(i, v, pi);
	}
	const Index* index(uint i) const {
		return vect_[i].ind;
	}
	const vector<uint>* values(uint i) const {
		return vect_[i].values;
	}
	const vector<uint> values(uint i, const vector<uint>& k) const {
		vector<uint> ret;
		for (uint i = 0; i < vect_.size(); ++ i) {
			ret.push_back(vect_[i].values->at(k[i]));
		}
		return ret;
	}
	uint proofsSize(uint i) const {
		return vect_[i].proofsSize;
	}
	const vector<uint>& obligatory(uint i) const {
		return vect_[i].obligatory;
	}
	const vector<uint>& proofInds(uint i) const {
		return vect_[i].proofInds;
	}
	const vector<IndexPtr>& vect() const {
		return vect_;
	}
	void clear() {
		vect_.clear();
	}
	uint card() const {
		uint ret = 1;
		for (const auto& i : vect_) {
			ret *= i.proofsSize;
		}
		return ret;
	}
	string show() const;

private:
	vector<IndexPtr> vect_;
};

VectorUnified unify(const VectorIndex& vindex);

string show(const VectorIndex& vindex);

extern bool debug_multy_index;
extern bool debug_multy_index_1;

}}}


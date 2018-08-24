#pragma once

#include "rus_prover_index.hpp"

namespace mdl { namespace rus { namespace prover {

typedef map<vector<uint>, Subst> MultyUnifiedSubs;
typedef map<vector<uint>, LightTree> MultyUnifiedTerms;

struct VectorIndex {
	struct IndexPtr {
		IndexPtr(const Index* i, const vector<uint>* v, uint ps) : ind(i), values(v), proofsSize(ps) { }
		IndexPtr(const IndexPtr&) = default;
		IndexPtr& operator = (const IndexPtr&) = default;
		const Index* ind;
		const vector<uint>* values;
		uint proofsSize;
	};
	uint size() const {
		return vect_.size();
	}
	void add(const IndexInt& i, uint ps) {
		vect_.emplace_back(&i.index(), &i.data(), ps);
	}
	void add(const Index* i, const vector<uint>* v, uint ps) {
		vect_.emplace_back(i, v, ps);
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
	const vector<IndexPtr>& vect() const {
		return vect_;
	}
	void clear() {
		vect_.clear();
	}

private:
	vector<IndexPtr> vect_;
};

MultyUnifiedTerms unify(const VectorIndex& vindex, MultyUnifiedSubs& unif);

string show(const VectorIndex& vindex);
string show(const set<uint>&);
string show(const vector<uint>&);
string show(const MultyUnifiedSubs&);
string show(const MultyUnifiedTerms&);

extern bool debug_multy_index;

}}}


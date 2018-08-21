#pragma once

#include "rus_prover_index.hpp"

namespace mdl { namespace rus { namespace prover {

typedef map<vector<uint>, Subst> MultyUnifiedSubs;
typedef map<vector<uint>, LightTree> MultyUnifiedTerms;
typedef set<vector<uint>> Restrictions;

struct VectorIndex {
	struct IndexPtr {
		IndexPtr(const Index* i, const vector<uint>* v) : ind(i), values(v) { }
		IndexPtr(const IndexPtr&) = default;
		IndexPtr& operator = (const IndexPtr&) = default;
		const Index* ind;
		const vector<uint>* values;
	};
	uint size() const {
		return vect_.size();
	}
	void add(const IndexInt& i) {
		vect_.emplace_back(&i.index(), &i.data());
	}
	void add(const Index* i, const vector<uint>* v) {
		vect_.emplace_back(i, v);
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
	const vector<IndexPtr>& vect() const { return vect_; }


private:
	vector<IndexPtr> vect_;
};

MultyUnifiedTerms unify(const VectorIndex& vindex, MultyUnifiedSubs& unif, const Restrictions* restrictions = nullptr);

string show(const VectorIndex& vindex);
string show(const set<uint>&);
string show(const vector<uint>&);
string show(const MultyUnifiedSubs&);
string show(const MultyUnifiedTerms&);

extern bool debug_multy_index;

}}}


#pragma once

#include "rus_prover_index.hpp"

namespace mdl { namespace rus { namespace prover {

struct VectorIndex {
	struct IndexPtr {
		IndexPtr(const Index* i, const vector<uint>* v, uint ps, bool e, bool oblig) :
			ind(i), values(v), proofsSize(ps), empty(e) {
			if (oblig) {
				set<uint> vals;
				for (auto val : *values) {
					vals.insert(val);
				}
				for (uint i = 0; i < proofsSize; ++ i) {
					if (vals.find(i) == vals.end()) {
						obligatory.push_back(i);
					}
				}
			}
		}
		IndexPtr(const IndexPtr&) = default;
		IndexPtr& operator = (const IndexPtr&) = default;
		const Index* ind;
		const vector<uint>* values;
		uint proofsSize;
		const bool empty;
		vector<uint> obligatory;
	};
	uint size() const {
		return vect_.size();
	}
	void add(const IndexInt& i, uint ps) {
		vect_.emplace_back(&i.index(), &i.data(), ps, i.index().size == 0, true);
	}
	void add(const Index* i, const vector<uint>* v, uint ps, bool em) {
		vect_.emplace_back(i, v, ps, em, true);
	}
	bool empty(uint i) const {
		return vect_[i].empty;
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
	const vector<IndexPtr>& vect() const {
		return vect_;
	}
	void clear() {
		vect_.clear();
	}
	string show() const {
		string ret;
		for (uint i = 0; i < vect_.size(); ++ i) {
			const IndexPtr& ptr = vect_[i];
			ret += string("Index: ") + to_string(i) + "\n";
			ret += string("Values: ");
			if (ptr.values) {
				for (uint j = 0; j < ptr.values->size(); ++j) {
					ret += to_string(ptr.values->at(j)) + ", ";
				}
				ret += "\n";
			} else {
				ret += "NULL\n";
			}
			ret += string("Obligatory: ");
			for (uint j = 0; j < ptr.obligatory.size(); ++j) {
				ret += to_string(ptr.obligatory.at(j)) + ", ";
			}
			ret += "\n";
			ret += string("Proofs size: ") + to_string(ptr.proofsSize) + "\n";
			ret += string("Index size: ") + (ptr.ind ? to_string(ptr.ind->size) : "NULL") + "\n";
			ret += string("Empty: ") + (ptr.empty ? "yes" : "no") + "\n";
			ret += string("Index: ");
			if (ptr.ind) {
				ret += ptr.ind->show();
			} else {
				ret += "NULL\n";
			}
			ret += "\n";
		}
		return ret;
	}

private:
	vector<IndexPtr> vect_;
};

struct SubstTree {
	Subst     sub;
	LightTree tree;
};

typedef map<vector<uint>, Subst> MultyUnifiedSubs;
typedef map<vector<uint>, SubstTree> VectorUnified;

VectorUnified unify(const VectorIndex& vindex);

string show(const VectorIndex& vindex);
string show(const set<uint>&);
string show(const vector<uint>&);
string show(const VectorUnified&);
string show(const MultyUnifiedSubs&);

extern bool debug_multy_index;
extern bool debug_multy_index_1;

}}}


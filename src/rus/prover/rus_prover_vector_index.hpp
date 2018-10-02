#pragma once

#include "rus_prover_tree_index.hpp"
#include "rus_prover_vector_unified.hpp"
#include "rus_prover_product_unified.hpp"

namespace mdl { namespace rus { namespace prover {

struct VectorIndex {
	struct LeafsInfo {
		LeafsInfo(const vector<uint>* v, const vector<uint>& pi) :
			values(v), proofsSize(pi.size()), proofInds(pi) {
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
		LeafsInfo(const LeafsInfo& li) = default;
		uint proofsSize;
		const vector<uint>* values;
		vector<uint> obligatory;
		vector<uint> proofInds;
	};
	struct IndexPtr {
		IndexPtr(const TreeIndex* i, const vector<uint>* v, const vector<uint>& pi) : ind(i), info(v, pi) { }
		IndexPtr(const TreeIndex* i, const LeafsInfo& li) : ind(i), info(li) { }
		IndexPtr(const IndexPtr&) = default;
		IndexPtr& operator = (const IndexPtr&) = default;
		const TreeIndex* ind;
		LeafsInfo info;
	};
	uint size() const {
		return vect_.size();
	}
	void add(const IndexInt& i, const vector<uint>& pi) {
		vect_.emplace_back(&i.index(), &i.data(), pi);
	}
	void add(const TreeIndex* i, const LeafsInfo& li) {
		vect_.emplace_back(i, li);
	}
	const TreeIndex* index(uint i) const {
		return vect_[i].ind;
	}
	const LeafsInfo& info(uint i) const {
		return vect_[i].info;
	}
	uint card() const {
		uint ret = 1;
		for (const auto& i : vect_) {
			ret *= i.info.proofsSize;
		}
		return ret;
	}
	string show() const;

private:
	vector<IndexPtr> vect_;
};

struct VectorProductUnified {
	string show() const {
		string ret;
		ret += "VECTOR:\n";
		ret += vect.show() + "\n";
		ret += "PROCUT:\n";
		ret += prod.show() + "\n\n";
		return ret;
	}
	void finalize(ProdVect leafs, const vector<LightSymbol>& w, const LightTree& t, bool may_add) {
		static uint c = 0;
		c++;
		vect.finalize(leafs, w, t);
		prod.finalize(leafs, w, t);
		/*if (!verify()) {
			cout << "AAA: " << c << endl;
			exit(1);
		}*/
	}
	void add_intersection(const vector<VectorProductUnified>& v, const Rule* r, const vector<LightSymbol>& w) {
		vector<VectorUnified> vects;
		vector<ProductUnified> prods;
		for (const auto& x : v) {
			vects.push_back(x.vect);
			prods.push_back(x.prod);
		}
		static uint c = 0;
		c++;
		/*if (c == 29263) {
			cout << "rule: " << Lex::toStr(r->id()) << endl;
			cout << "w: ";
			for (auto s : w) {
				cout << prover::show(s) << " ";
			}
			cout << endl;
			cout << "VectorUnifieds:" << endl;
			uint i = 0;
			for (const auto& vu : prods) {
				cout << "VECTOR UNIFIED: " << i++ << endl;
				cout << vu.show() << endl << endl << endl << endl;
			}
			debug_union_vect = true;
		}*/

		vect.add_intersection(vects, r, w);
		prod.add_intersection(prods, r, w);
		if (!verify()) {
			cout << "AFTER " << endl;
			cout << "VectorUnifieds:" << endl;
			cout << prod.show() << endl;
			cout << "BBB: " << c << endl;
			exit(1);
		}
	}
	std::map<vector<uint>, SubstTree> map() const {
		return prod.map();
	}

	bool verify() const {
		if (debug_union_vect) {
			if (vect.map() != prod.map()) {
				std::map<vector<uint>, SubstTree> vmap = vect.map();
				std::map<vector<uint>, SubstTree> pmap = prod.map();
				cout << "vect.map() != prod.map()" << endl;
				for (const auto& p : vmap) {
					if (pmap.count(p.first) == 0) {
						cout << "prod map doesn't have key: " << prover::show(p.first) << endl;
					} else if (pmap[p.first] != p.second) {
						cout << "values of key: " << prover::show(p.first) << " are different" << endl;
						cout << "pmap:" << endl << pmap[p.first].show();
						cout << "vmap:" << endl << vmap[p.first].show();
					}
				}
				for (const auto& p : pmap) {
					if (vmap.count(p.first) == 0) {
						cout << "vect map doesn't have key: " << prover::show(p.first) << endl;
					} else if (vmap[p.first] != p.second) {
						cout << "values of key: " << prover::show(p.first) << " are different" << endl;
						cout << "pmap:" << endl << pmap[p.first].show();
						cout << "vmap:" << endl << vmap[p.first].show();
					}
				}
				cout << "end of check" << endl;
				return false;
			}
		}
		return true;
	}

private:
	friend MultyUnifiedSubs intersect(const std::map<LightSymbol, VectorProductUnified>& terms, MultyUnifiedSubs& unif);
	VectorUnified  vect;
	ProductUnified prod;
};

inline MultyUnifiedSubs intersect(const std::map<LightSymbol, VectorProductUnified>& terms, MultyUnifiedSubs& unif) {
	std::map<LightSymbol, VectorUnified> vect_map;
	for (const auto& p : terms) {
		vect_map[p.first] = p.second.vect;
	}
	return intersect(vect_map, unif);
}

//typedef VectorUnified ResultUnified;
typedef ProductUnified ResultUnified;
//typedef VectorProductUnified ResultUnified;

ResultUnified unify(const VectorIndex& vindex);

string show(const VectorIndex& vindex);

extern bool debug_multy_index;
extern bool debug_multy_index_1;

}}}


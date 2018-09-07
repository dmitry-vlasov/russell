#pragma once

#include "rus_prover_index.hpp"
#include "rus_prover_product_vector.hpp"

namespace mdl { namespace rus { namespace prover {

string show(const set<uint>&);
string show(const vector<uint>&);

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
	string show() const {
		string ret;
		ret += "expr: " + prover::show(tree) + "\n";
		ret += Indent::paragraph(prover::show(sub)) + "\n";
		return ret;
	}
};

template<class Data>
struct VectorMap {
	map<vector<uint>, Data> map_;
};

template<class D>
VectorMap<vector<D>> intersect(const vector<const VectorMap<D>*>& v) {
	VectorMap<vector<D>> ret;
	for (const auto& p : v[0]->map_) {
		vector<uint> k = p.first;
		vector<D> data;
		for (const auto& m : v) {
			auto i = m->map_.find(k);
			if (i != m->map_.end() && !i->second.tree.empty()) {
				data.push_back(i->second);
			}
		}
		if (data.size() == v.size()) {
			ret.map_[k] = data;
		}
	}
	return ret;
}

struct VectorUnified {

	string show() const {
		ostringstream oss;
		for (const auto& u : unif_.map_) {
			oss << prover::show(u.first) << " --> " << endl;
			oss << "term: " << prover::show(u.second.tree) << endl;
			oss << "sub: " << prover::show(u.second.sub) << endl;
		}
		return oss.str();
	}

	void finalize(ProdVect leafs_vect, const vector<LightSymbol>& w, const LightTree& t) {
		CartesianProd<uint> leafs_prod = leafsProd(leafs_vect);
		if (leafs_prod.card() == 0) {
			return;
		}
		while (true) {
			vector<uint> leafs = leafs_prod.data();
			finalize(leafs, w, t);
			if (!leafs_prod.hasNext()) {
				break;
			}
			leafs_prod.makeNext();
		}
	}

	void add_intersection(const vector<VectorUnified>& v, const Rule* r, const vector<LightSymbol>& w) {
		vector<const VectorMap<SubstTree>*> maps;
		for (const auto& m : v) {
			maps.push_back(&m.unif_);
		}
		VectorMap<vector<SubstTree>> common = intersect(maps);
		for (const auto& p : common.map_) {
			vector<SubstTree> subtrees;

			LightTree::Children children;
			Subst unif;
			for (const auto& st : subtrees) {
				unif = unify_subs(MultySubst({&unif, &st.sub}));
				if (!unif.ok) {
					break;
				}
				children.push_back(make_unique<LightTree>(st.tree));
			}
			if (children.size() == r->arity()) {
				if (unif_.map_[p.first].sub.compose(unif)) {
					LightTree term = apply(unif, LightTree(r, children));
					finalize(p.first, w, term);
				}
			}
		}
	}

	std::map<vector<uint>, SubstTree>& map() { return unif_.map_; }
	const std::map<vector<uint>, SubstTree>& map() const { return unif_.map_; }


	void finalize(const vector<uint> leafs, const vector<LightSymbol>& w, const LightTree& t) {
		if (w.size()) {
			LightTree term = unify_step(unif_.map_[leafs].sub, w, t);
			if (!term.empty()) {
				unif_.map_[leafs].tree = apply(unif_.map_[leafs].sub, term);
			} else {
			}
		} else {
			unif_.map_[leafs].sub;
			unif_.map_[leafs].tree = apply(unif_.map_[leafs].sub, t);
		}
	}
private:
	CartesianProd<uint> leafsProd(const ProdVect& leafs) {
		CartesianProd<uint> leafs_prod;
		for (uint i = 0; i < leafs.vect.size(); ++ i) {
			leafs_prod.incSize();
			for (uint l : leafs[i].set()) {
				leafs_prod.incDim(l);
			}
		}
		return leafs_prod;
	}

	VectorMap<SubstTree> unif_;
};

VectorUnified unify(const VectorIndex& vindex);

string show(const VectorIndex& vindex);

extern bool debug_multy_index;
extern bool debug_multy_index_1;

}}}


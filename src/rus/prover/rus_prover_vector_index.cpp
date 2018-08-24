#include "rus_prover_cartesian.hpp"
#include "rus_prover_unify.hpp"
#include "rus_prover_leafs.hpp"
#include "rus_prover_vector_index.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_multy_index = false;

typedef vector<const Index::Leaf*> LeafVector;

inline bool complete(const LeafVector& v) {
	for (auto x : v) {
		if (!x) {
			return false;
		}
	}
	return true;
}

CartesianProd<uint> leafsProd(const VectorIndex& vi, const LeafVector& leafs) {
	assert(complete(leafs));
	CartesianProd<uint> leafs_prod;
	for (uint i = 0; i < leafs.size(); ++ i) {
		leafs_prod.incSize();
		if (!leafs[i]) {
			cout << "NULL LEAF" << endl;
			assert(false);
		}
		for (uint s : leafs[i]->inds) {
			uint ind = vi.values(i)->at(s);
			leafs_prod.incDim(ind);
		}
	}
	return leafs_prod;
}

struct MIndexSpace {
	set<LightSymbol> symbs;
	set<const Rule*> rules;
	CartesianProd<LightSymbol> vars_prod;

	const VectorIndex& vindex;
	MultyUnifiedSubs& unif;
	MultyUnifiedTerms terms;
	LeafVector fixed;

	MIndexSpace(const VectorIndex& vi, MultyUnifiedSubs& un, const LeafVector& f) :
	vindex(vi), unif(un), fixed(f) {
		for (uint i = 0; i < vindex.size(); ++ i) {
			vars_prod.incSize();
			if (fixed[i]) {
				vars_prod.skip(i);
			} else {
				for (const auto& p : vindex.index(i)->vars) {
					if (p.first.rep) {
						vars_prod.incDim(p.first);
					}
					symbs.insert(p.first);
				}
				for (const auto& p : vindex.index(i)->rules) {
					rules.insert(p.first);
				}
			}
		}
	}

	void finalize(LeafVector leafs_vect, const vector<LightSymbol>& w, const LightTree& t) {
		assert(complete(leafs_vect));
		CartesianProd<uint> leafs_prod = leafsProd(vindex, leafs_vect);
		if (leafs_prod.card() == 0) {
			return;
		}
		while (true) {

			vector<uint> leafs = leafs_prod.data();
			if (leafs.size() != vindex.size()) {
				cout << "AAA" << endl;
				assert(false);
			}
			cout << "LEAFS: " << prover::show(leafs) << endl;
			if (w.size()) {
				LightTree unified = unify_step(unif[leafs], w, t);
				if (!unified.empty()) {
					terms[leafs] = unified;
				}
			} else {
				unif[leafs];
				terms[leafs] = t;
			}
			if (!leafs_prod.hasNext()) {
				break;
			}
			leafs_prod.makeNext();
		}
	}
};

MultyUnifiedTerms unify(const VectorIndex& vindex, MultyUnifiedSubs& unif, const LeafVector& fixed);

void unify_symbs(MIndexSpace& space)
{
	for (LightSymbol s : space.symbs) {
		CartesianProd<LightSymbol> vars_prod = space.vars_prod;
		LeafVector s_leafs = space.fixed;
		for (uint i = 0; i < space.vindex.size(); ++ i) {
			if (space.vindex.index(i)->vars.count(s)) {
				vars_prod.skip(i);
				s_leafs[i] = &space.vindex.index(i)->vars.at(s);
			}
		}
		if (vars_prod.card() > 0) {
			while (true) {
				vector<LightSymbol> w = vars_prod.data();
				vector<uint> inds = vars_prod.indexes();
				LeafVector w_leafs = s_leafs;
				for (uint i = 0; i < space.vindex.size(); ++ i) {
					if (inds[i] != -1) {
						w_leafs[i] = &space.vindex.index(i)->vars.at(w[inds[i]]);
					}
				}
				space.finalize(w_leafs, w, LightTree(s));
				if (!vars_prod.hasNext()) {
					break;
				}
				vars_prod.makeNext();
			}
		}
		if (complete(s_leafs)) {
			// All indexes have variable 'v'
			space.finalize(s_leafs, vector<LightSymbol>(), LightTree(s));
		}
	}
}

void unify_leaf_rule(MIndexSpace& space, const Rule* r)
{
	assert(r->arity() == 0);
	CartesianProd<LightSymbol> vars_prod = space.vars_prod;
	LeafVector r_leafs = space.fixed;
	for (uint i = 0; i < space.vindex.size(); ++ i) {
		if (space.vindex.index(i)->rules.count(r)) {
			vars_prod.skip(i);
			r_leafs[i] = &space.vindex.index(i)->rules.at(r).leaf();
		}
	}
	if (vars_prod.card() > 0) {
		while (true) {
			vector<LightSymbol> w = vars_prod.data();
			vector<uint> inds = vars_prod.indexes();
			LeafVector w_leafs = r_leafs;
			for (uint i = 0; i < space.vindex.size(); ++ i) {
				if (inds[i] != -1) {
					w_leafs[i] = &space.vindex.index(i)->vars.at(w[inds[i]]);
				}
			}
			space.finalize(w_leafs, w, LightTree(r, {}));
			if (!vars_prod.hasNext()) {
				break;
			}
			vars_prod.makeNext();
		}
	}
	if (complete(r_leafs)) {
		// All indexes have rule 'r'
		space.finalize(r_leafs, vector<LightSymbol>(), LightTree(r, {}));
	}
}

void unify_branch_rule(MIndexSpace& space, const Rule* r, const LeafVector& leafs)
{
	vector<MultyUnifiedTerms> child_terms(r->arity());
	VectorIndex child_vindex;
	for (uint k = 0; k < r->arity(); ++ k) {
		child_vindex.clear();
		for (uint i = 0; i < space.vindex.size(); ++ i) {
			if (!leafs[i]) {
				if (!space.vindex.index(i)->rules.count(r)) {
					return;
				}
				const Index* ind = space.vindex.index(i)->rules.at(r).branch().child[k].get();
				child_vindex.add(ind, space.vindex.values(i), space.vindex.proofsSize(i));
			} else {
				child_vindex.add(space.vindex.index(i), space.vindex.values(i), space.vindex.proofsSize(i));
			}
		}
		child_terms[k] = unify(child_vindex, space.unif, leafs);
	}
	for (const auto& p : child_terms[0]) {
		LightTree::Children children;
		for (uint i = 0; i < r->arity(); ++ i) {
			if (child_terms[i].count(p.first)) {
				children.push_back(make_unique<LightTree>(child_terms[i][p.first]));
			} else {
				break;
			}
		}
		if (children.size() == r->arity()) {
			space.terms[p.first] = LightTree(r, children);
		}
	}
}

void unify_rules(MIndexSpace& space)
{
	for (const Rule* r : space.rules) {
		if (r->arity() == 0) {
			unify_leaf_rule(space, r);
			continue;
		}
		CartesianProd<LightSymbol> vars_prod = space.vars_prod;
		while (true) {
			vector<LightSymbol> w = vars_prod.data();
			vector<uint> inds = vars_prod.indexes();
			LeafVector w_leafs = space.fixed;
			for (uint i = 0; i < space.vindex.size(); ++ i) {
				if (inds[i] != -1) {
					w_leafs[i] = &space.vindex.index(i)->vars.at(w[inds[i]]);
				}
			}
			unify_branch_rule(space, r, w_leafs);
			if (!vars_prod.hasNext()) {
				break;
			}
			vars_prod.makeNext();
		}
	}
}

MultyUnifiedTerms unify(const VectorIndex& vindex, MultyUnifiedSubs& unif, const LeafVector& fixed)
{
	MIndexSpace space(vindex, unif, fixed);
	unify_symbs(space);
	unify_rules(space);
	return space.terms;
}

MultyUnifiedTerms unify(const VectorIndex& vindex, MultyUnifiedSubs& unif) {
	return unify(vindex, unif, LeafVector(vindex.size(), nullptr));
}

}}}

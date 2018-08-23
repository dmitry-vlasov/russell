#include "rus_prover_cartesian.hpp"
#include "rus_prover_unify.hpp"
#include "rus_prover_leafs.hpp"
#include "rus_prover_vector_index.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_multy_index = false;

typedef vector<const Index::Leaf*> LeafVector;

inline bool leafs_are_complete(const LeafVector& v) {
	for (auto x : v) {
		if (!x) {
			return false;
		}
	}
	return true;
}

CartesianProd<uint> leafsProd(const VectorIndex& vi, const LeafVector& leafs) {
	assert(leafs_are_complete(leafs));
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

inline void insert_position(vector<bool>& vect, uint i, uint s) {
	if (!vect.size()) {
		vect = vector<bool>(s, false);
	}
	vect[i] = true;
}

struct MIndexSpace {
	MIndexSpace(const VectorIndex& vi, MultyUnifiedSubs& un, const LeafVector& f, const Restrictions* r) :
	total_size(vi.size()), active_size(0), fixed_size(0), vindex(vi), unif(un), fixed(f), restrictions(r)
	{
		for (uint i = 0; i < vindex.size(); ++ i) {
			if (fixed[i]) {
				++fixed_size;
			} else {
				++active_size;
				vars_prod.incSize();
				VectorIndex::IndexPtr ptrs = vindex.vect()[i];
				for (const auto& p : ptrs.ind->vars) {
					if (p.first.rep) {
						insert_position(vars[p.first], i, total_size);
						vars_prod.incDim(p.first);
					} else {
						insert_position(consts[p.first], i, total_size);
					}
					insert_position(symbs[p.first], i, total_size);
				}
				for (const auto& p : ptrs.ind->rules) {
					insert_position(rules[p.first], i, total_size);
				}
			}
		}
	}

	void finalize(LeafVector leafs_vect, const vector<LightSymbol>& w, const LightTree& t, const Subst& sub = Subst()) {
		CartesianProd<uint> leafs_prod = leafsProd(vindex, leafs_vect);
		if (leafs_prod.card() == 0) {
			return;
		}
		while (true) {
			vector<uint> leafs = leafs_prod.data();
			if (!restrictions || restrictions->count(leafs)) {
				if (w.size()) {
					LightTree unified = unify_step(unif[leafs], w, t);
					if (!unified.empty()) {
						Subst s = unif[leafs];
						if (s.compose(sub)) {
							if (terms.count(leafs)) {
								cout << "MULTIPLE UNIFICATION RESULTS" << endl;
								cout << "try_variable_replacement" << endl;
							}
							unif[leafs] = s.compose(sub);
							terms[leafs] = unified;
						}
					}
				} else {
					unif[leafs];
					terms[leafs] = t;
				}
			}
			if (!leafs_prod.hasNext()) {
				break;
			}
			leafs_prod.makeNext();
		}
	}

	map<LightSymbol, vector<bool>> vars;
	map<LightSymbol, vector<bool>> consts;
	map<LightSymbol, vector<bool>> symbs;
	map<const Rule*, vector<bool>> rules;
	CartesianProd<LightSymbol> vars_prod;

	uint total_size;
	uint active_size;
	uint fixed_size;
	const VectorIndex& vindex;
	MultyUnifiedSubs& unif;
	MultyUnifiedTerms terms;
	LeafVector fixed;
	const Restrictions* restrictions;
};

MultyUnifiedTerms unify(const VectorIndex& vindex, MultyUnifiedSubs& unif, const LeafVector& fixed, const Restrictions* restrictions = nullptr);

void unify_symbs(MIndexSpace& space)
{
	for (auto p : space.symbs) {
		LightSymbol s = p.first;
		CartesianProd<LightSymbol> vars_prod = space.vars_prod;
		LeafVector s_leafs = space.fixed;
		for (uint i = 0; i < space.total_size; ++ i) {
			if (space.vindex.index(i)->vars.count(s)) {
				vars_prod.skip(i);
				s_leafs[i] = &space.vindex.index(i)->vars.at(s);
			}
		}
		if (vars_prod.card() > 0) {
			while (true) {
				vector<LightSymbol> w = vars_prod.data();
				LeafVector w_leafs = s_leafs;
				for (uint i = 0; i < space.total_size; ++ i) {
					if (space.vindex.index(i)->vars.count(w[i])) {
						w_leafs[i] = &space.vindex.index(i)->vars.at(w[i]);
					}
				}
				space.finalize(w_leafs, w, LightTree(s));
				if (!vars_prod.hasNext()) {
					break;
				}
				vars_prod.makeNext();
			}
		}
		if (leafs_are_complete(s_leafs)) {
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
	for (uint i = 0; i < space.total_size; ++ i) {
		if (space.vindex.index(i)->rules.count(r)) {
			r_leafs[i] = &space.vindex.index(i)->rules.at(r).leaf();
		}
	}
	if (vars_prod.card() > 0) {
		while (true) {
			vector<LightSymbol> w = vars_prod.data();
			LeafVector w_leafs = r_leafs;
			for (uint i = 0; i < space.total_size; ++ i) {
				if (space.vindex.index(i)->vars.count(w[i])) {
					w_leafs[i] = &space.vindex.index(i)->vars.at(w[i]);
				}
			}
			space.finalize(w_leafs, w, LightTree(r, {}));
			if (!vars_prod.hasNext()) {
				break;
			}
			vars_prod.makeNext();
		}
	}
	if (leafs_are_complete(r_leafs)) {
		// All indexes have rule 'r'
		space.finalize(r_leafs, vector<LightSymbol>(), LightTree(r, {}));
	}
}

void unify_branch_rule(MIndexSpace& space, const Rule* r, const LeafVector& leafs)
{
	vector<MultyUnifiedTerms> child_terms(r->arity());
	VectorIndex child_vindex;
	for (uint i = 0; i < space.total_size; ++ i) {
		const Index* ind =
			space.vindex.index(i)->rules.count(r) ?
			space.vindex.index(i)->rules.at(r).branch().child[0].get() :
			nullptr;
		child_vindex.add(ind, space.vindex.values(i));
	}
	child_terms[0] = unify(child_vindex, space.unif, leafs, space.restrictions);
	Restrictions common;
	for (const auto& p : child_terms[0]) {
		common.insert(p.first);
	}
	for (uint k = 1; k < r->arity(); ++ k) {
		child_vindex.clear();
		for (uint i = 0; i < space.total_size; ++ i) {
			const Index* ind =
				space.vindex.index(i)->rules.count(r) ?
				space.vindex.index(i)->rules.at(r).branch().child[k].get() :
				nullptr;
			child_vindex.add(ind, space.vindex.values(i));
		}
		child_terms[k] = unify(child_vindex, space.unif, leafs, &common);
		common.clear();
		for (const auto& p : child_terms[k]) {
			common.insert(p.first);
		}
	}
	for (const auto& c : common) {
		LightTree::Children childern;
		for (uint i = 0; i < r->arity(); ++ i) {
			childern.push_back(make_unique<LightTree>(child_terms[i][c]));
		}
		space.terms[c] = LightTree(r, childern);
	}
}

void unify_rules(MIndexSpace& space)
{
	for (auto p : space.rules) {
		const Rule* r = p.first;
		if (r->arity() == 0) {
			unify_leaf_rule(space, r);
			continue;
		}
		CartesianProd<LightSymbol> vars_prod = space.vars_prod;
		while (true) {
			vector<LightSymbol> w = vars_prod.data();
			LeafVector w_leafs = space.fixed;
			for (uint i = 0; i < space.total_size; ++ i) {
				if (space.vindex.index(i)->vars.count(w[i])) {
					w_leafs[i] = &space.vindex.index(i)->vars.at(w[i]);
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

MultyUnifiedTerms unify(const VectorIndex& vindex, MultyUnifiedSubs& unif, const LeafVector& fixed, const Restrictions* restrictions)
{
	MIndexSpace space(vindex, unif, fixed, restrictions);
	unify_symbs(space);
	unify_rules(space);
	return space.terms;
}

MultyUnifiedTerms unify(const VectorIndex& vindex, MultyUnifiedSubs& unif, const Restrictions* restrictions) {
	return unify(vindex, unif, LeafVector(vindex.size(), nullptr), restrictions);
}

}}}


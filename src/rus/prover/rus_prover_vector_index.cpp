#include "rus_prover_cartesian.hpp"
#include "rus_prover_unify.hpp"
#include "rus_prover_leafs.hpp"
#include "rus_prover_vector_index.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_multy_index = false;

typedef vector<const Index::Leaf*> LeafVector;

string show_leafs(const LeafVector& leafs) {
	string ret;
	for (auto l : leafs) {
		if (l) {
			ret += show(l->inds) + ", ";
		} else {
			ret += "NULL, ";
		}
	}
	return ret;
}

inline bool complete(const LeafVector& v, const VectorIndex& vi) {
	for (uint i = 0; i < v.size(); ++i) {
		if (!v[i] && /*!vi.empty(i)*/ vi.index(i)) {
			return false;
		}
	}
	return true;
}

CartesianProd<uint> leafsProd(const VectorIndex& vi, const LeafVector& leafs) {
	assert(complete(leafs, vi) && "leafsProd(const VectorIndex& vi, const LeafVector& leafs)");
	CartesianProd<uint> leafs_prod;
	for (uint i = 0; i < leafs.size(); ++ i) {
		leafs_prod.incSize();
		if (!leafs[i]) {
			for (uint ind = 0; ind < vi.proofsSize(i); ++ind) {
				leafs_prod.incDim(ind);
			}
		} else {
			for (uint s : leafs[i]->inds) {
				uint ind = vi.values(i)->at(s);
				leafs_prod.incDim(ind);
			}
		}
	}
	return leafs_prod;
}

struct MIndexSpace {
	VectorUnified unified;
	set<LightSymbol> symbs;
	set<const Rule*> rules;
	CartesianProd<LightSymbol> vars_prod;

	const VectorIndex& vindex;
	LeafVector fixed;
	uint depth;

	MIndexSpace(const VectorIndex& vi, const LeafVector& f, uint d) :
	vindex(vi), fixed(f), depth(d) {
		for (uint i = 0; i < vindex.size(); ++ i) {
			vars_prod.incSize();
			if (fixed[i] || !vindex.index(i)) {
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
		assert(complete(leafs_vect, vindex));
		CartesianProd<uint> leafs_prod = leafsProd(vindex, leafs_vect);
		if (leafs_prod.card() == 0) {
			return;
		}
		while (true) {
			vector<uint> leafs = leafs_prod.data();
			if (w.size()) {
				Subst unif = unified[leafs].sub;
				LightTree term = unify_step(unif, w, t);
				if (!term.empty()) {
					unified[leafs].sub = unif;
					unified[leafs].tree = term;
				}
			} else {
				unified[leafs].sub;
				unified[leafs].tree = t;
			}
			if (!leafs_prod.hasNext()) {
				break;
			}
			leafs_prod.makeNext();
		}
	}
};

void unify_symbs(MIndexSpace& space)
{
	for (LightSymbol s : space.symbs) {
		CartesianProd<LightSymbol> vars_prod = space.vars_prod;
		LeafVector s_leafs = space.fixed;
		for (uint i = 0; i < space.vindex.size(); ++ i) {
			if (space.vindex.index(i) && space.vindex.index(i)->vars.count(s)) {
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
					if (inds[i] != -1 && space.vindex.index(i)) {
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
		if (complete(s_leafs, space.vindex)) {
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
		if (space.vindex.index(i) && space.vindex.index(i)->rules.count(r)) {
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
				if (inds[i] != -1 && space.vindex.index(i)) {
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
	if (complete(r_leafs, space.vindex)) {
		// All indexes have rule 'r'
		space.finalize(r_leafs, vector<LightSymbol>(), LightTree(r, {}));
	}
}

VectorUnified unify(const VectorIndex& vindex, const LeafVector& fixed, uint depth);

void unify_branch_rule(MIndexSpace& space, const Rule* r, const LeafVector& leafs)
{
	/*cout << "PARENT VINDEX:" << endl;
	cout << Indent::paragraph(space.vindex.show(), space.depth) << endl;
	cout << "LEAFS: " << endl;
	cout << "\t" << show_leafs(leafs) << endl;*/

	vector<VectorUnified> child_terms(r->arity());
	for (uint k = 0; k < r->arity(); ++ k) {
		VectorIndex child_vindex;
		for (uint i = 0; i < space.vindex.size(); ++ i) {
			if (!leafs[i] && space.vindex.index(i) && !space.vindex.empty(i)) {
				if (!space.vindex.index(i)->rules.count(r)) {
					return;
				}
				const Index* ind = space.vindex.index(i)->rules.at(r).branch().child[k].get();
				child_vindex.add(ind, space.vindex.values(i), space.vindex.proofsSize(i), space.vindex.empty(i));
			} else {
				child_vindex.add(nullptr, space.vindex.values(i), space.vindex.proofsSize(i), space.vindex.empty(i));
			}
		}

		//cout << "CHILD VINDEX:" << endl;
		//cout << Indent::paragraph(child_vindex.show(), space.depth + 1) << endl;

		child_terms[k] = unify(child_vindex, leafs, space.depth + 1);
	}
	for (const auto& p : child_terms[0]) {
		LightTree::Children children;
		Subst unif;
		for (uint i = 0; i < r->arity(); ++ i) {
			if (child_terms[i].count(p.first)) {
				children.push_back(make_unique<LightTree>(child_terms[i][p.first].tree));
				if (!unif.compose(child_terms[i][p.first].sub)) {
					break;
				}
			} else {
				break;
			}
		}
		if (children.size() == r->arity()) {
			space.unified[p.first].tree = LightTree(r, children);
			space.unified[p.first].sub = unif;
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
		unify_branch_rule(space, r, space.fixed);
		CartesianProd<LightSymbol> vars_prod = space.vars_prod;
		while (true) {
			vector<LightSymbol> w = vars_prod.data();
			vector<uint> inds = vars_prod.indexes();
			LeafVector w_leafs = space.fixed;
			for (uint i = 0; i < space.vindex.size(); ++ i) {
				if (inds[i] != -1 && space.vindex.index(i)) {
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

VectorUnified unify(const VectorIndex& vindex, const LeafVector& fixed, uint depth)
{
	MIndexSpace space(vindex, fixed, depth);
	unify_symbs(space);
	unify_rules(space);
	return space.unified;
}

VectorUnified unify(const VectorIndex& vindex) {
	return unify(vindex, LeafVector(vindex.size(), nullptr), 0);
}

}}}

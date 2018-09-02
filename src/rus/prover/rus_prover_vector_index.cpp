#include "rus_prover_cartesian.hpp"
#include "rus_prover_unify.hpp"
#include "rus_prover_leafs.hpp"
#include "rus_prover_vector_index.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_multy_index = false;
bool debug_multy_index_1 = false;

struct LeafStorage {
	bool init(const Index::Leaf& ind_leafs, const vector<uint>* ind_values) {
		if (leafs.size() > 0) {
			cout << "AAAA" << endl;
			cout << "old_leafs: " << show(leafs) << endl;
			cout << "ind_values: " << show(*ind_values) << endl;
			cout << "ind_leafs: " << show(ind_leafs.inds) << endl;
			vector<uint> new_leafs;
			for (uint s : ind_leafs.inds) {
				new_leafs.push_back(ind_values->at(s));
			}
			cout << "new_leafs: " << show(leafs) << endl;
			//throw Error("AAA");
		}
		if (!leafs.empty()) {
			return false;
		}
		//assert(leafs.size() == 0 && "LeafStorage::init");
		leafs.clear();
		for (uint s : ind_leafs.inds) {
			leafs.push_back(ind_values->at(s));
		}
		return true;
	}
	void init(uint l) {
		leafs.push_back(l);
	}
	vector<uint> leafs;
};

typedef vector<LeafStorage> LeafVector;

string show_leafs(const LeafVector& leafs) {
	string ret;
	for (auto l : leafs) {
		if (l.leafs.size()) {
			ret += show(l.leafs) + ", ";
		} else {
			ret += "empty, ";
		}
	}
	return ret;
}

inline bool complete(const LeafVector& v, const VectorIndex& vi) {
	for (uint i = 0; i < v.size(); ++i) {
		if (!v[i].leafs.size() && vi.index(i)) {
			return false;
		}
	}
	return true;
}

vector<bool> intersect(const vector<bool>& s1, const vector<bool>& s2) {
	vector<bool> ret(s1.size(), false);
	for (uint i = 0; i < s1.size(); ++ i) {
		ret[i] == s1[i] && s2[i];
	}
	return ret;
}

CartesianProd<uint> leafsProd(const VectorIndex& vi, const LeafVector& leafs) {
	assert(complete(leafs, vi) && "leafsProd(const VectorIndex& vi, const LeafVector& leafs)");
	CartesianProd<uint> leafs_prod;
	for (uint i = 0; i < leafs.size(); ++ i) {
		leafs_prod.incSize();
		for (uint l : leafs[i].leafs) {
			leafs_prod.incDim(l);
		}
	}
	return leafs_prod;
}

struct MIndexSpace {
	VectorUnified unified;
	set<LightSymbol> symbs;
	set<const Rule*> rules;
	CartesianProd<LightSymbol> vars_prod;

	map<LightSymbol, vector<bool>> symb_inds;
	map<const Rule*, vector<bool>> rule_inds;
	vector<bool> vars_inds;

	const VectorIndex& vindex;
	LeafVector fixed;
	uint depth;

	bool complete(const vector<bool>& s) const {
		for (uint i = 0; i < vindex.size(); ++ i) {
			if (fixed[i].leafs.size()) {
				continue;
			}
			if (!s.at(i) && !vars_inds.at(i)) {
				return false;
			}
		}
		return true;
	}
	bool complete_for(LightSymbol s) const {
		return complete(symb_inds.at(s));
	}
	bool complete_for(const Rule* r) const {
		return complete(rule_inds.at(r));
	}

	MIndexSpace(const VectorIndex& vi, const LeafVector& f, uint d) :
	vars_inds(vi.size(), false), vindex(vi), fixed(f), depth(d) {
		for (uint i = 0; i < vindex.size(); ++ i) {
			vars_prod.incSize();
			if (fixed[i].leafs.size() || !vindex.index(i)) {
				vars_prod.skip(i);
			} else {
				for (const auto& p : vindex.index(i)->vars) {
					if (p.first.rep) {
						vars_prod.incDim(p.first);
						vars_inds[i] = true;
					}
					symbs.insert(p.first);
					if (!symb_inds.count(p.first)) {
						symb_inds[p.first] = vector<bool>(vi.size(), false);
					}
					symb_inds[p.first][i] = true;
				}
				for (const auto& p : vindex.index(i)->rules) {
					rules.insert(p.first);
					if (!rule_inds.count(p.first)) {
						rule_inds[p.first] = vector<bool>(vi.size(), false);
					}
					rule_inds[p.first][i] = true;
				}
			}
		}
	}

	void finalize(LeafVector leafs_vect, const vector<LightSymbol>& w, const LightTree& t) {
		assert(prover::complete(leafs_vect, vindex));
		CartesianProd<uint> leafs_prod = leafsProd(vindex, leafs_vect);
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

	void finalize(const vector<uint> leafs, const vector<LightSymbol>& w, const LightTree& t) {
		if (w.size()) {
			if (debug_multy_index_1) {
				cout << "PRE FINAL: " << show(leafs) << " TERM: " << show(t) << endl;
				cout << Indent::paragraph(show(unified[leafs].sub)) << endl;
			}
			LightTree term = unify_step(unified[leafs].sub, w, t);
			if (!term.empty()) {
				unified[leafs].tree = term;
			}
			if (debug_multy_index_1) {
				cout << "FINAL: " << show(leafs) << " TERM: " << show(term) << endl;
				cout << Indent::paragraph(show(unified[leafs].sub)) << endl;
			}

		} else {
			unified[leafs].sub;
			unified[leafs].tree = t;
		}
	}
};

void unify_symbs_variant(MIndexSpace& space, LightSymbol s, const vector<bool>& not_vars)
{
	CartesianProd<LightSymbol> vars_prod = space.vars_prod;
	LeafVector s_leafs = space.fixed;
	for (uint i = 0; i < space.vindex.size(); ++ i) {
		//if (space.vindex.index(i) && space.vindex.index(i)->vars.count(s)) {
		if (not_vars.at(i)) {
			vars_prod.skip(i);
			if (s_leafs[i].leafs.empty()) {
				s_leafs[i].init(space.vindex.index(i)->vars.at(s), space.vindex.values(i));
			}
		}
	}
	if (vars_prod.card() > 0) {
		while (true) {
			vector<LightSymbol> w = vars_prod.data();
			vector<uint> inds = vars_prod.indexes();
			LeafVector w_leafs = s_leafs;
			for (uint i = 0; i < space.vindex.size(); ++ i) {
				if (inds[i] != -1 && space.vindex.index(i)) {
					w_leafs[i].init(space.vindex.index(i)->vars.at(w[inds[i]]), space.vindex.values(i));
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


void unify_symbs(MIndexSpace& space)
{
	for (LightSymbol s : space.symbs) {
		LeafVector s_leafs = space.fixed;
		if (!space.complete_for(s)) {
			continue;
		}
		vector<bool> common = intersect(space.vars_inds, space.symb_inds.at(s));
		PowerSetIter ps_iter;
		for (uint i = 0; i < space.vindex.size(); ++ i) {
			if (common.at(i)) {
				ps_iter.addDim();
			} else {
				ps_iter.addSkipped();
			}
		}
		if (ps_iter.card() > 0) {
			while (true) {
				vector<bool> not_vars = ps_iter.values();
				unify_symbs_variant(space, s, not_vars);
				if (!ps_iter.hasNext()) {
					break;
				}
				ps_iter.makeNext();
			}
		} else {
			unify_symbs_variant(space, s, space.symb_inds.at(s));
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
			r_leafs[i].init(space.vindex.index(i)->rules.at(r).leaf(), space.vindex.values(i));
		}
	}
	if (vars_prod.card() > 0) {
		while (true) {
			vector<LightSymbol> w = vars_prod.data();
			vector<uint> inds = vars_prod.indexes();
			LeafVector w_leafs = r_leafs;
			for (uint i = 0; i < space.vindex.size(); ++ i) {
				if (inds[i] != -1 && space.vindex.index(i)) {
					w_leafs[i].init(space.vindex.index(i)->vars.at(w[inds[i]]), space.vindex.values(i));
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

void unify_branch_rule(MIndexSpace& space, const Rule* r, const vector<LightSymbol>& w, const LeafVector& leafs)
{
	/*if (debug_multy_index_1) {
		cout << "PARENT VINDEX:" << endl;
		cout << Indent::paragraph(space.vindex.show(), space.depth) << endl;
		cout << "LEAFS: " << endl;
		cout << "\t" << show_leafs(leafs) << endl;
	}*/

	vector<VectorUnified> child_terms(r->arity());
	for (uint k = 0; k < r->arity(); ++ k) {
		VectorIndex child_vindex;
		for (uint i = 0; i < space.vindex.size(); ++ i) {
			if (!leafs[i].leafs.size() && space.vindex.index(i) && !space.vindex.empty(i)) {
				if (!space.vindex.index(i)->rules.count(r)) {
					return;
				}
				const Index* ind = space.vindex.index(i)->rules.at(r).branch().child[k].get();
				child_vindex.add(ind, space.vindex.values(i), space.vindex.proofInds(i), space.vindex.empty(i));
			} else {
				child_vindex.add(nullptr, space.vindex.values(i), space.vindex.proofInds(i), space.vindex.empty(i));
			}
		}

		/*if (debug_multy_index_1) {
			cout << "CHILD VINDEX:" << endl;
			cout << Indent::paragraph(child_vindex.show(), space.depth + 1) << endl;
		}*/

		child_terms[k] = unify(child_vindex, leafs, space.depth + 1);
	}
	for (const auto& p : child_terms[0]) {
		LightTree::Children children;
		Subst unif;
		for (uint i = 0; i < r->arity(); ++ i) {
			if (child_terms[i].count(p.first)) {

				if (debug_multy_index_1) {
					cout << "COMPOSING:" << endl;
					cout << "UNIF: " << endl << show(unif) << endl;
					cout << "child_terms[i][p.first].sub: " << endl << show(child_terms[i][p.first].sub) << endl;
				}

				if (!unif.compose(child_terms[i][p.first].sub)) {
					if (debug_multy_index_1) {
						cout << "FAILURE" << endl;
					}
					break;
				} else {
					if (debug_multy_index_1) {
						cout << "SUCCESS" << endl;
						cout << "UNIF: " << endl << show(unif) << endl << endl;
					}
				}
				children.push_back(make_unique<LightTree>(child_terms[i][p.first].tree));
			} else {
				break;
			}
		}
		if (children.size() == r->arity()) {
			if (space.unified[p.first].sub.compose(unif)) {
				space.finalize(p.first, w, LightTree(r, children));
			}
		}
	}
}

void unify_rules(MIndexSpace& space)
{
	for (const Rule* r : space.rules) {
		if (r->arity() == 0) {
			if (space.complete_for(r)) {
				unify_leaf_rule(space, r);
			}
			continue;
		}
		unify_branch_rule(space, r, vector<LightSymbol>(), space.fixed);
		CartesianProd<LightSymbol> vars_prod = space.vars_prod;
		while (true) {
			vector<LightSymbol> w = vars_prod.data();
			vector<uint> inds = vars_prod.indexes();
			LeafVector w_leafs = space.fixed;
			for (uint i = 0; i < space.vindex.size(); ++ i) {
				if (inds[i] != -1 && space.vindex.index(i)) {
					w_leafs[i].init(space.vindex.index(i)->vars.at(w[inds[i]]), space.vindex.values(i));
				}
			}
			unify_branch_rule(space, r, w, w_leafs);
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

vector<map<uint, uint>> back_values(const VectorIndex& vindex) {
	vector<map<uint, uint>> ret(vindex.size());
	for (uint i = 0; i < vindex.size(); ++ i) {
		for (uint j = 0; j < vindex.values(i)->size(); ++ j) {
			ret[i][vindex.values(i)->at(j)] = j;
		}
	}
	return ret;
}

bool check_vector_index_unified(const vector<uint>& leafs, const SubstTree& subtree, const VectorIndex& vindex) {
	vector<map<uint, uint>> b_values = back_values(vindex);
	vector<uint> expr_ind(vindex.size());
	for (uint i = 0; i < vindex.size(); ++ i) {
		if (b_values[i].count(leafs[i])) {
			expr_ind[i] = b_values[i][leafs[i]];
		} else {
			expr_ind[i] = -1;
		}
	}
	LightTree common;
	for (uint i = 0; i < vindex.size(); ++ i) {
		if (expr_ind[i] != -1) {
			LightTree e_orig = vindex.index(i)->exprs[expr_ind[i]];
			if (apply(subtree.sub, e_orig) != subtree.tree) {
				cout << "VECTOR INDEX UNIFICATION FAILS" << endl;
				cout << show(apply(subtree.sub, e_orig)) << " != " << show(subtree.tree) << endl << endl;
				cout << "e_orig: " << show(e_orig) << endl;
				cout << "subtree.tree: " << show(subtree.tree) << endl;
				cout << "subtree.sub: " << show(subtree.sub) << endl;
				return false;
			}
			if (!common.empty() && common != subtree.tree) {
				cout << "VECTOR INDEX UNIFICATION FAILS" << endl;
				cout << show(common) << " != " << show(subtree.tree) << endl << endl;
				cout << "common: " << show(common) << endl;
				cout << "e_orig: " << show(e_orig) << endl;
				cout << "subtree.tree: " << show(subtree.tree) << endl;
				cout << "subtree.sub: " << show(subtree.sub) << endl;
				return false;
			} else {
				common = subtree.tree;
			}
		}
	}
	return true;
}

VectorUnified unify(const VectorIndex& vindex) {
	CartesianProd<uint> absent_leafs_prod;
	for (uint i = 0; i < vindex.size(); ++ i) {
		absent_leafs_prod.incSize();
		if (vindex.obligatory(i).size()) {
			absent_leafs_prod.incDim(0);
			for (uint a : vindex.obligatory(i)) {
				absent_leafs_prod.incDim(a + 1);
			}
		} else {
			absent_leafs_prod.skip(i);
		}
	}
	MIndexSpace space(vindex, LeafVector(vindex.size()), 0);
	while (true) {
		space.fixed = LeafVector(vindex.size());
		vector<uint> absent_leafs = absent_leafs_prod.data();
		vector<uint> absent_inds = absent_leafs_prod.indexes();
		for (uint i = 0; i < vindex.size(); ++ i) {
			if (absent_inds[i] != -1) {
				uint a = absent_leafs[absent_inds[i]];
				if (a > 0) {
					space.fixed[i].init(a - 1);
				}
			}
		}
		try{
		unify_symbs(space);
		unify_rules(space);
		} catch (Error& e) {
			cout << "*********" << endl;
			cout << "absent_leafs: " << show(absent_leafs) << endl;
			cout << "absent_inds: " << show(absent_inds) << endl;
			cout << "space.fixed: " << show_leafs(space.fixed) << endl;
			cout << endl;
			throw e;
		}
		if (!absent_leafs_prod.hasNext()) {
			break;
		}
		absent_leafs_prod.makeNext();
	}
	for (const auto& p : space.unified) {
		if (!check_vector_index_unified(p.first, p.second, vindex)) {
			throw Error("VECTOR UNIFICATION ERROR");
		}
	}
	return space.unified;
}

}}}

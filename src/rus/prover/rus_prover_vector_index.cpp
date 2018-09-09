#include "rus_prover_cartesian.hpp"
#include "rus_prover_unify.hpp"
#include "rus_prover_vector_index.hpp"
#include "rus_prover_product_vector.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_multy_index = false;
bool debug_multy_index_1 = false;
bool debug_multy_index_2 = false;

vector<bool> intersect(const vector<bool>& s1, const vector<bool>& s2) {
	vector<bool> ret(s1.size(), false);
	for (uint i = 0; i < s1.size(); ++ i) {
		ret[i] = s1[i] && s2[i];
	}
	return ret;
}

string show(const vector<bool>& v) {
	string ret;
	ret += "(";
	for (bool x : v) {
		ret += x ? "true, " : "false, ";
	}
	ret += ")";
	return ret;
}

string show(const vector<LightSymbol>& v) {
	string ret;
	ret += "(";
	for (auto s : v) {
		ret += prover::show(s) + ", ";
	}
	ret += ")";
	return ret;
}

struct MIndexSpace {
	ResultUnified unified;
	set<LightSymbol> symbs;
	set<const Rule*> rules;
	CartesianProd<LightSymbol> vars_prod;

	map<LightSymbol, vector<bool>> symb_inds;
	map<const Rule*, vector<bool>> rule_inds;
	vector<bool> vars_inds;

	const VectorIndex& vindex;
	ProdVect fixed;
	uint depth;

	MIndexSpace(const VectorIndex& vi, const ProdVect& f, uint d) :
	vars_inds(vi.size(), false), vindex(vi), fixed(f), depth(d) {
		for (uint i = 0; i < vindex.size(); ++ i) {
			vars_prod.incSize();
			if (fixed[i].storesInfo() || !vindex.index(i)) {
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

	string show() const {
		ostringstream oss;
		oss << "M_INDEX_SPACE" << endl;
		oss << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%" << endl;
		oss << "depth: " << depth << endl;
		oss << "ResultUnified: " << endl << "--------------" << endl;
		oss << unified.show();
		oss << endl;
		oss << "Symbs: {"; for (auto s : symbs) oss << prover::show(s) << ", "; oss << "}" << endl;
		oss << endl;
		oss << "Rules: {"; for (auto r : rules) oss << Lex::toStr(r->id()) << ", "; oss << "}" << endl;
		oss << endl;
		oss << "Vars prod:" << endl;
		oss << vars_prod.show() << endl;
		oss << endl;
		oss << "Symb inds: " << endl;
		for (const auto& p : symb_inds) {
			oss << "\t" << prover::show(p.first) << " --> " << prover::show(p.second) << endl;
		}
		oss << endl;
		oss << "Rule inds: " << endl;
		for (const auto& p : rule_inds) {
			oss << "\t" << Lex::toStr(p.first->id()) << " --> " << prover::show(p.second) << endl;
		}
		oss << endl;
		oss << "Var inds: " << prover::show(vars_inds) << endl;
		oss << endl;
		oss << "VIndex: " << endl;
		oss << vindex.show() << endl;
		oss << endl;
		oss << "Fixed:" << endl;
		oss << fixed.show() << endl;
		oss << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%" << endl;
		return oss.str();
	}

	bool complete(const vector<bool>& s) const {
		for (uint i = 0; i < vindex.size(); ++ i) {
			if (fixed[i].storesInfo()) {
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
	bool complete(const ProdVect& v) const {
		for (uint i = 0; i < vindex.size(); ++i) {
			if (!v[i].storesInfo() && vindex.index(i)) {
				return false;
			}
		}
		return true;
	}
};

void unify_symbs_variant(MIndexSpace& space, LightSymbol s, const vector<bool>& s_fixed)
{
	CartesianProd<LightSymbol> vars_prod = space.vars_prod;
	ProdVect s_leafs = space.fixed;
	for (uint i = 0; i < space.vindex.size(); ++ i) {
		if (s_leafs[i].storesInfo()) {
			vars_prod.skip(i);
			if (s_fixed.at(i)) {
				return;
			}
		} else {
			if (s_fixed.at(i)) {
				vars_prod.skip(i);
				if (!s_leafs[i].init(space.vindex.index(i)->vars.at(s), space.vindex.values(i))) {
					return;
				}
			}
		}
	}
	if (vars_prod.card() > 0) {
		while (true) {
			vector<LightSymbol> w = vars_prod.data();
			vector<uint> inds = vars_prod.indexes();
			ProdVect w_leafs = s_leafs;
			bool consistent = true;
			for (uint i = 0; i < space.vindex.size(); ++ i) {
				if (inds[i] != -1 && space.vindex.index(i)) {
					if (!w_leafs[i].init(space.vindex.index(i)->vars.at(w[inds[i]]), space.vindex.values(i))) {
						consistent = false;
						break;
					}
				}
			}
			if (consistent) {
				space.unified.finalize(w_leafs, w, LightTree(s));
			}
			if (!vars_prod.hasNext()) {
				break;
			}
			vars_prod.makeNext();
		}
	}
	if (space.complete(s_leafs)) {
		// All indexes have variable 'v'
		space.unified.finalize(s_leafs, vector<LightSymbol>(), LightTree(s));
	}
}


void unify_symbs(MIndexSpace& space)
{
	for (LightSymbol s : space.symbs) {
		ProdVect s_leafs = space.fixed;
		if (!space.complete_for(s)) {
			continue;
		}
		vector<bool> common = intersect(space.vars_inds, space.symb_inds.at(s));
		PowerSetIter ps_iter;
		for (uint i = 0; i < space.vindex.size(); ++ i) {
			if (s_leafs[i].storesInfo()) {
				ps_iter.addSkipped();
			} else {
				if (common.at(i)) {
					ps_iter.addDim();
				} else if (space.symb_inds.at(s)[i]) {
					ps_iter.addFixed(true);
				} else {
					ps_iter.addSkipped();
				}
			}
		}
		if (ps_iter.card() > 0) {
			while (true) {
				if (!ps_iter.initial()) {
					vector<bool> s_fixed = ps_iter.values();
					unify_symbs_variant(space, s, s_fixed);
				}
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

void unify_leaf_rule_variant(MIndexSpace& space, const Rule* r, const vector<bool>& r_fixed)
{
	assert(r->arity() == 0);
	CartesianProd<LightSymbol> vars_prod = space.vars_prod;
	ProdVect r_leafs = space.fixed;
	for (uint i = 0; i < space.vindex.size(); ++ i) {
		if (r_leafs[i].storesInfo()) {
			vars_prod.skip(i);
			if (r_fixed.at(i)) {
				return;
			}
		} else {
			if (r_fixed.at(i)) {
				vars_prod.skip(i);
				if (!r_leafs[i].init(space.vindex.index(i)->rules.at(r).leaf(), space.vindex.values(i))) {
					return;
				}
			}
		}
	}
	if (vars_prod.card() > 0) {
		while (true) {
			vector<LightSymbol> w = vars_prod.data();
			vector<uint> inds = vars_prod.indexes();
			ProdVect w_leafs = r_leafs;
			bool consistent = true;
			for (uint i = 0; i < space.vindex.size(); ++ i) {
				if (inds[i] != -1 && space.vindex.index(i)) {
					if (!w_leafs[i].init(space.vindex.index(i)->vars.at(w[inds[i]]), space.vindex.values(i))) {
						consistent = false;
						break;
					}
				}
			}
			if (consistent) {
				space.unified.finalize(w_leafs, w, LightTree(r, {}));
			}
			if (!vars_prod.hasNext()) {
				break;
			}
			vars_prod.makeNext();
		}
	}
	if (space.complete(r_leafs)) {
		// All indexes have rule 'r'
		space.unified.finalize(r_leafs, vector<LightSymbol>(), LightTree(r, {}));
	}
}


void unify_leaf_rule(MIndexSpace& space, const Rule* r)
{
	assert(r->arity() == 0);
	if (!space.complete_for(r)) {
		return;
	}
	vector<bool> common = intersect(space.vars_inds, space.rule_inds.at(r));
	PowerSetIter ps_iter;
	for (uint i = 0; i < space.vindex.size(); ++ i) {
		if (space.fixed[i].storesInfo()) {
			ps_iter.addSkipped();
		} else {
			if (common.at(i)) {
				ps_iter.addDim();
			} else if (space.rule_inds.at(r)[i]) {
				ps_iter.addFixed(true);
			} else {
				ps_iter.addSkipped();
			}
		}
	}
	if (ps_iter.card() > 0) {
		while (true) {
			vector<bool> r_fixed = ps_iter.values();
			unify_leaf_rule_variant(space, r, r_fixed);
			if (!ps_iter.hasNext()) {
				break;
			}
			ps_iter.makeNext();
		}
	} else {
		unify_leaf_rule_variant(space, r, space.rule_inds.at(r));
	}
}

ResultUnified unify(const VectorIndex& vindex, const ProdVect& fixed, uint depth);

void unify_branch_rule(MIndexSpace& space, const Rule* r, const vector<LightSymbol>& w, const ProdVect& leafs)
{
	vector<ResultUnified> child_terms(r->arity());
	for (uint k = 0; k < r->arity(); ++ k) {
		VectorIndex child_vindex;
		for (uint i = 0; i < space.vindex.size(); ++ i) {
			if (space.vindex.index(i)) {
				if (!leafs[i].storesInfo() && !space.vindex.index(i)->rules.count(r)) {
					return;
				}
				const Index* ind =
					space.vindex.index(i)->rules.count(r) ?
					space.vindex.index(i)->rules.at(r).branch().child[k].get() : nullptr;
				child_vindex.add(ind, space.vindex.values(i), space.vindex.proofInds(i));
			} else {
				child_vindex.add(nullptr, space.vindex.values(i), space.vindex.proofInds(i));
			}
		}
		child_terms[k] = unify(child_vindex, leafs, space.depth + 1);
	}
	space.unified.add_intersection(child_terms, r, w);
}

void unify_rule_variant(MIndexSpace& space, const Rule* r, const vector<bool>& r_fixed)
{
	CartesianProd<LightSymbol> vars_prod = space.vars_prod;
	ProdVect r_leafs = space.fixed;
	for (uint i = 0; i < space.vindex.size(); ++ i) {
		if (r_leafs[i].storesInfo()) {
			vars_prod.skip(i);
			if (r_fixed.at(i)) {
				return;
			}
		} else {
			if (r_fixed.at(i)) {
				vars_prod.skip(i);
			}
		}
	}
	unify_branch_rule(space, r, vector<LightSymbol>(), r_leafs);

	while (true) {
		vector<LightSymbol> w = vars_prod.data();
		vector<uint> inds = vars_prod.indexes();
		ProdVect w_leafs = r_leafs;
		bool consistent = true;
		for (uint i = 0; i < space.vindex.size(); ++ i) {
			if (inds[i] != -1 && space.vindex.index(i)) {
				if (!w_leafs[i].init(space.vindex.index(i)->vars.at(w[inds[i]]), space.vindex.values(i))) {
					consistent = false;
					break;
				}
			}
		}
		if (consistent) {
			unify_branch_rule(space, r, w, w_leafs);
		}
		if (!vars_prod.hasNext()) {
			break;
		}
		vars_prod.makeNext();
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
		vector<bool> common = intersect(space.vars_inds, space.rule_inds.at(r));
		PowerSetIter ps_iter;
		for (uint i = 0; i < space.vindex.size(); ++ i) {
			if (space.fixed[i].storesInfo()) {
				ps_iter.addSkipped();
			} else {
				if (common.at(i)) {
					ps_iter.addDim();
				} else if (space.rule_inds.at(r)[i]) {
					ps_iter.addFixed(true);
				} else {
					ps_iter.addSkipped();
				}
			}
		}
		if (ps_iter.card() > 0) {
			while (true) {
				if (!ps_iter.initial()) {
					vector<bool> r_fixed = ps_iter.values();
					unify_rule_variant(space, r, r_fixed);
				}
				if (!ps_iter.hasNext()) {
					break;
				}
				ps_iter.makeNext();
			}
		} else {
			unify_rule_variant(space, r, space.rule_inds.at(r));
		}
	}
}

ResultUnified unify(const VectorIndex& vindex, const ProdVect& fixed, uint depth)
{
	MIndexSpace space(vindex, fixed, depth);
	if (debug_multy_index_1) {
		cout << space.show() << endl;
		debug_multy_index_1 = false;
	}
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
		if (expr_ind[i] != -1 && subtree.sub.ok) {
			LightTree e_orig = vindex.index(i)->exprs[expr_ind[i]];
			if (apply(subtree.sub, e_orig) != subtree.tree) {
				cout << "VECTOR INDEX UNIFICATION FAILS (A)" << endl;
				cout << show(apply(subtree.sub, e_orig)) << " != " << show(subtree.tree) << endl << endl;
				cout << "e_orig: " << show(e_orig) << endl;
				cout << "subtree.tree: " << show(subtree.tree) << endl;
				cout << "subtree.sub: " << show(subtree.sub) << endl;
				cout << "leafs: " << show(leafs) << endl;
				cout << "vindex:" << endl << vindex.show();
				return false;
			}
			if (!common.empty() && common != subtree.tree) {
				cout << "VECTOR INDEX UNIFICATION FAILS (B)" << endl;
				cout << show(common) << " != " << show(subtree.tree) << endl << endl;
				cout << "common: " << show(common) << endl;
				cout << "e_orig: " << show(e_orig) << endl;
				cout << "subtree.tree: " << show(subtree.tree) << endl;
				cout << "subtree.sub: " << show(subtree.sub) << endl;
				cout << "leafs: " << show(leafs) << endl;
				cout << "vindex:" << endl << vindex.show();
				return false;
			} else {
				common = subtree.tree;
			}
		}
	}
	return true;
}

ResultUnified unify(const VectorIndex& vindex) {
	PowerSetIter absent_iter;
	for (uint i = 0; i < vindex.size(); ++ i) {
		if (vindex.obligatory(i).size()) {
			absent_iter.addDim();
		} else {
			absent_iter.addSkipped();
		}
	}
	MIndexSpace space(vindex, ProdVect(vindex.size()), 0);
	while (true) {
		space.fixed = ProdVect(vindex.size());
		for (uint i = 0; i < vindex.size(); ++ i) {
			if (absent_iter[i]) {
				space.fixed[i].init(vindex.obligatory(i));
			}
		}
		if (space.complete(space.fixed)) {
			space.unified.finalize(space.fixed, vector<LightSymbol>(), LightTree());
		} else {
			unify_symbs(space);
			unify_rules(space);
		}
		if (!absent_iter.hasNext()) {
			break;
		}
		absent_iter.makeNext();
	}
	for (const auto& p : space.unified.map()) {
		if (!check_vector_index_unified(p.first, p.second, vindex)) {
			throw Error("VECTOR UNIFICATION ERROR");
		}
	}
	return space.unified;
}

string VectorIndex::show() const {
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

}}}

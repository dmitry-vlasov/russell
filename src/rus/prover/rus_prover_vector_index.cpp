#include "rus_prover_cartesian.hpp"
#include "rus_prover_unify.hpp"
#include "rus_prover_leafs.hpp"
#include "rus_prover_vector_index.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_multy_index = false;
bool debug_multy_index_1 = false;
bool debug_multy_index_2 = false;

struct LeafStorage {
	LeafStorage() : index_leafs(nullptr) { }

	bool init(const Index::Leaf& ind_leafs, const vector<uint>* ind_values) {
		if (!index_leafs) {
			index_leafs = &ind_leafs;
			for (uint s : ind_leafs.inds) {
				leafs.push_back(ind_values->at(s));
			}
			return true;
		} else {
			return index_leafs == &ind_leafs;
		}
	}

	void init(uint l) {
		leafs.push_back(l);
	}

	void init(const vector<uint>& l) {
		leafs = l;
	}

	vector<uint> leafs;

private:
	const Index::Leaf* index_leafs;
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

vector<bool> intersect(const vector<bool>& s1, const vector<bool>& s2) {
	vector<bool> ret(s1.size(), false);
	for (uint i = 0; i < s1.size(); ++ i) {
		ret[i] = s1[i] && s2[i];
	}
	return ret;
}

bool false_vector(const vector<bool>& s) {
	for (uint i = 0; i < s.size(); ++ i) {
		if (s.at(i)) {
			return false;
		}
	}
	return true;
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

	string show() const {
		ostringstream oss;
		oss << "M_INDEX_SPACE" << endl;
		oss << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%" << endl;
		oss << "depth: " << depth << endl;
		oss << "VectorUnified: " << endl << "--------------" << endl;
		for (const auto& u : unified) {
			oss << prover::show(u.first) << " --> " << endl;
			oss << "term: " << prover::show(u.second.tree) << endl;
			oss << "sub: " << prover::show(u.second.sub) << endl;
		}
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
		oss << show_leafs(fixed) << endl;
		oss << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%" << endl;
		return oss.str();
	}

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
		assert(complete(leafs_vect));
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

	void finalize(const vector<uint> leafs, const vector<LightSymbol>& w, const LightTree& t) {
		static uint c = 0;
		if (debug_multy_index) {
			/*if (prover::show(leafs) == "(6, 32, 28, )") {
				++c;
				if (c == 15) {
					cout << "DDD" << endl;
				}
				cout << "FUCK " << c << endl;
				cout << "w: "; for (auto s: w) cout << prover::show(s) << ", "; cout << endl;
				cout << "t: " << prover::show(t) << endl;
				cout << "sub: " << prover::show(unified[leafs].sub) << endl;
				cout << "leafs: " << prover::show(leafs) << endl;
			}*/
		}
		if (w.size()) {
			LightTree term = unify_step(unified[leafs].sub, w, t);
			if (!term.empty()) {
				/*if (debug_multy_index && prover::show(leafs) == "(6, 32, 28, )") {
					cout << "SUCCESS (A)" << endl;
					cout << "sub: " << prover::show(unified[leafs].sub) << endl;
				}*/

				if (!unified[leafs].tree.empty() && unified[leafs].tree != term) {
				//if (debug_multy_index) {
					//cout << "!unified[leafs].tree.empty()" << endl;
					if (!unified[leafs].tree.empty() && unified[leafs].tree != term) {
						cout << "555555555555" << endl;
					}
					cout << "unified[" << prover::show(leafs) << "].tree: " << prover::show(unified[leafs].tree) << endl;
					cout << "term: " << prover::show(term) << endl;
					cout << "sub: " << prover::show(unified[leafs].sub) << endl;
					//cout << "leafs: " << prover::show(leafs) << endl;
				}

				unified[leafs].tree = apply(unified[leafs].sub, term);
			} else {
				/*if (debug_multy_index && prover::show(leafs) == "(6, 32, 28, )") {
					cout << "FAILURE" << endl;
					cout << "sub: " << prover::show(unified[leafs].sub) << endl;
				}*/
			}
		} else {
			unified[leafs].sub;
			unified[leafs].tree = apply(unified[leafs].sub, t);
			/*if (debug_multy_index && prover::show(leafs) == "(6, 32, 28, )") {
				cout << "SUCCESS (B)" << endl;
				cout << "unified[" << prover::show(leafs) << "].tree: " << prover::show(unified[leafs].tree) << endl;
				cout << "sub: " << prover::show(unified[leafs].sub) << endl;
			}*/
		}
		/*if (debug_multy_index && prover::show(leafs) == "(6, 32, 28, )") {
			cout << "---------------" << endl;
		}*/
	}

	bool complete(const LeafVector& v) const {
		for (uint i = 0; i < vindex.size(); ++i) {
			if (!v[i].leafs.size() && vindex.index(i)) {
				return false;
			}
		}
		return true;
	}

private:
	CartesianProd<uint> leafsProd(const LeafVector& leafs) {
		assert(complete(leafs) && "leafsProd(const VectorIndex& vi, const LeafVector& leafs)");
		CartesianProd<uint> leafs_prod;
		for (uint i = 0; i < leafs.size(); ++ i) {
			leafs_prod.incSize();
			for (uint l : leafs[i].leafs) {
				leafs_prod.incDim(l);
			}
		}
		return leafs_prod;
	}
};

void unify_symbs_variant(MIndexSpace& space, LightSymbol s, const vector<bool>& s_fixed)
{
	CartesianProd<LightSymbol> vars_prod = space.vars_prod;
	LeafVector s_leafs = space.fixed;
	for (uint i = 0; i < space.vindex.size(); ++ i) {
		if (s_leafs[i].leafs.size()) {
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
	if (debug_multy_index) {
		//cout << "s_leafs: " << show_leafs(s_leafs) << endl;
		//cout << "s_fixed: " << show(s_fixed) << endl;
	}
	if (vars_prod.card() > 0) {
		while (true) {
			vector<LightSymbol> w = vars_prod.data();
			vector<uint> inds = vars_prod.indexes();
			LeafVector w_leafs = s_leafs;
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
				if (debug_multy_index) {
					//cout << "w_leafs: " << show_leafs(w_leafs) << endl;
				}
				space.finalize(w_leafs, w, LightTree(s));
			}
			if (!vars_prod.hasNext()) {
				break;
			}
			vars_prod.makeNext();
		}
	}
	if (space.complete(s_leafs)) {
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
			if (s_leafs[i].leafs.size()) {
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
			if (debug_multy_index) {
				//cout << "FFFFFFFFFFFFFFFF" << endl;
			}
			while (true) {
				vector<bool> s_fixed = ps_iter.values();
				if (debug_multy_index) {
					//cout << "ps_iter: " << ps_iter.show() << endl;
				}
				if (!false_vector(s_fixed)) {
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
		//unify_symbs_variant(space, s, space.symb_inds.at(s));
	}
}

void unify_leaf_rule_variant(MIndexSpace& space, const Rule* r, const vector<bool>& r_fixed)
{
	assert(r->arity() == 0);
	CartesianProd<LightSymbol> vars_prod = space.vars_prod;
	LeafVector r_leafs = space.fixed;
	for (uint i = 0; i < space.vindex.size(); ++ i) {
		if (r_leafs[i].leafs.size()) {
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
			LeafVector w_leafs = r_leafs;
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
				space.finalize(w_leafs, w, LightTree(r, {}));
			}
			if (!vars_prod.hasNext()) {
				break;
			}
			vars_prod.makeNext();
		}
	}
	if (space.complete(r_leafs)) {
		// All indexes have rule 'r'
		space.finalize(r_leafs, vector<LightSymbol>(), LightTree(r, {}));
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
		if (space.fixed[i].leafs.size()) {
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
		if (debug_multy_index) {
			cout << "GGGGGGGGGGGGGGG" << endl;
		}
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

VectorUnified unify(const VectorIndex& vindex, const LeafVector& fixed, uint depth);

void unify_branch_rule(MIndexSpace& space, const Rule* r, const vector<LightSymbol>& w, const LeafVector& leafs)
{
	vector<VectorUnified> child_terms(r->arity());
	for (uint k = 0; k < r->arity(); ++ k) {
		VectorIndex child_vindex;
		for (uint i = 0; i < space.vindex.size(); ++ i) {
			if (space.vindex.index(i)) {
				if (!leafs[i].leafs.size() && !space.vindex.index(i)->rules.count(r)) {
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

		/*if (debug_multy_index && Lex::toStr(r->id()) == "wi") {
			cout << "WI: " << endl;
			cout << child_vindex.show() << endl;
			debug_multy_index_1 = true;
			debug_multy_index_2 = true;
		}*/
		/*if (debug_multy_index && Lex::toStr(r->id()) == "wn") {
			cout << "WN: " << endl;
			cout << child_vindex.show() << endl;
			debug_multy_index_1 = true;
		}*/

		child_terms[k] = unify(child_vindex, leafs, space.depth + 1);

		/*if (debug_multy_index && Lex::toStr(r->id()) == "wi") {
			cout << "WI RESULT: " << endl;
			cout << show(child_terms[k]) << endl;
		}*/
		/*
		if (debug_multy_index && Lex::toStr(r->id()) == "wn") {
			cout << "WN RESULT: " << endl;
			cout << show(child_terms[k]) << endl;
		}*/
	}
	for (const auto& p : child_terms[0]) {
		LightTree::Children children;
		Subst unif;
		for (uint i = 0; i < r->arity(); ++ i) {
			if (child_terms[i].count(p.first) && !child_terms[i][p.first].tree.empty()) {

				//Subst s = unify_subs(unif, child_terms[i][p.first].sub);
				unif = unify_subs(MultySubst({&unif, &child_terms[i][p.first].sub}));

				//if (!unif.compose(child_terms[i][p.first].sub)) {
				if (!unif.ok) {

					if (debug_multy_index && show(p.first) == "(1, 1, )") {
						cout << "(A)FUCK!!!" << endl;
						cout << Indent::paragraph(show(child_terms[i][p.first].sub)) << endl;
						cout << Indent::paragraph(show(unif)) << endl;
						cout << "FAIL" << endl;
					}

					break;
				} else {
					if (debug_multy_index && show(p.first) == "(1, 1, )") {
						cout << "(A)FUCK!!!" << endl << "SUCCESS" << endl;
					}
				}
				children.push_back(make_unique<LightTree>(child_terms[i][p.first].tree));
			} else {
				break;
			}
		}
		if (children.size() == r->arity()) {
			if (space.unified[p.first].sub.compose(unif)) {
				LightTree term = apply(unif, LightTree(r, children));
				space.finalize(p.first, w, term);
				if (debug_multy_index && show(p.first) == "(1, 1, )") {
					cout << "(B)FUCK!!!" << endl;
					cout << "term: " << show(term) << endl;
					cout << "sub:" << endl;
					cout << Indent::paragraph(show(space.unified[p.first].sub)) << endl;
					cout << "SUCCESS" << endl;
				}
			} else {
				if (debug_multy_index && show(p.first) == "(1, 1, )") {
					cout << "(B)FUCK!!!" << endl;
					cout << Indent::paragraph(show(space.unified[p.first].sub)) << endl;
					cout << Indent::paragraph(show(unif)) << endl;
					cout << "FAIL" << endl;
				}
			}
		}
	}
}

void unify_rule_variant(MIndexSpace& space, const Rule* r, const vector<bool>& r_fixed)
{
	CartesianProd<LightSymbol> vars_prod = space.vars_prod;
	LeafVector r_leafs = space.fixed;
	for (uint i = 0; i < space.vindex.size(); ++ i) {
		if (r_leafs[i].leafs.size()) {
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
		LeafVector w_leafs = r_leafs;
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
			if (space.fixed[i].leafs.size()) {
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
			if (debug_multy_index) {
				//cout << "HHHHHHHHHHHHHHH" << endl;
			}
			while (true) {
				vector<bool> r_fixed = ps_iter.values();
				if (!false_vector(r_fixed)) {
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
		//unify_rule_variant(space, r, space.rule_inds.at(r));
	}
}

VectorUnified unify(const VectorIndex& vindex, const LeafVector& fixed, uint depth)
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

VectorUnified unify(const VectorIndex& vindex) {
	PowerSetIter absent_iter;
	for (uint i = 0; i < vindex.size(); ++ i) {
		if (vindex.obligatory(i).size()) {
			absent_iter.addDim();
		} else {
			absent_iter.addSkipped();
		}
	}
	MIndexSpace space(vindex, LeafVector(vindex.size()), 0);
	while (true) {
		space.fixed = LeafVector(vindex.size());
		for (uint i = 0; i < vindex.size(); ++ i) {
			if (absent_iter[i]) {
				space.fixed[i].init(vindex.obligatory(i));
			}
		}
		if (space.complete(space.fixed)) {
			space.finalize(space.fixed, vector<LightSymbol>(), LightTree());
		} else {
			unify_symbs(space);
			unify_rules(space);
		}
		if (!absent_iter.hasNext()) {
			break;
		}
		absent_iter.makeNext();
	}
	for (const auto& p : space.unified) {
		if (!check_vector_index_unified(p.first, p.second, vindex)) {
			throw Error("VECTOR UNIFICATION ERROR");
		}
	}
	return space.unified;
}

}}}

#include "rus_prover_cartesian.hpp"
#include "rus_prover_unify.hpp"
#include "rus_prover_leafs.hpp"
#include "rus_prover_vector_index.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_multy_index = false;

void unify_vars_step(
	const VectorIndex& vindex,
	const vector<LightSymbol>& w,
	const LightTree& t,
	MultyUnifiedSubs& unif,
	MultyUnifiedTerms& terms,
	const set<vector<uint>>* restrictions,
	const vector<uint>& other_leafs = vector<uint>(),
	const set<uint>& other_indexes = set<uint>(),
	const Subst& other_subst = Subst())
{
	CartesianProd<uint> leafs_prod;
	for (uint i = 0; i < w.size(); ++ i) {
		leafs_prod.incSize();
		if (!other_indexes.count(i)) {
			if (vindex.index(i)->vars.count(w[i])) {
				for (uint s : vindex.index(i)->vars.at(w[i])) {
					leafs_prod.incDim(s);
				}
			}
		} else {
			leafs_prod.skip(i);
		}
	}
	if (leafs_prod.card() == 0) {
		return;
	}
	while (true) {
		vector<uint> leafs = join_leafs(other_leafs, leafs_prod.data(), other_indexes);
		if (!restrictions || restrictions->count(leafs)) {
			LightTree unified = unify_step(unif[leafs], w, t);
			if (!unified.empty()) {
				Subst s = unif[leafs];
				if (s.compose(other_subst)) {
					if (terms.count(leafs)) {
						cout << "MULTIPLE UNIFICATION RESULTS" << endl;
						cout << "try_variable_replacement" << endl;
					}
					unif[leafs] = s;
					terms[leafs] = unified;
				}
			}
		}
		if (!leafs_prod.hasNext()) {
			break;
		}
		leafs_prod.makeNext();
	}
}


void unify_const_step(
	const VectorIndex& vindex,
	LightSymbol c,
	MultyUnifiedSubs& unif,
	MultyUnifiedTerms& terms,
	const set<vector<uint>>* restrictions)
{
	CartesianProd<uint> leafs_prod;
	for (const auto& i : vindex.vect()) {
		leafs_prod.incSize();
		for (uint s : i.ind->vars.at(c)) {
			leafs_prod.incDim(s);
		}
	}
	if (leafs_prod.card() == 0) {
		return;
	}
	while (true) {
		vector<uint> leafs = leafs_prod.data();
		if (!restrictions || restrictions->count(leafs)) {
			unif[leafs];
			terms[leafs] = LightTree(c);
		}
		if (!leafs_prod.hasNext()) {
			break;
		}
		leafs_prod.makeNext();
	}
}

void unify_rule_step(
	const VectorIndex& vindex,
	const rus::Rule* r,
	MultyUnifiedSubs& unif,
	MultyUnifiedTerms& terms,
	const set<vector<uint>>* restrictions)
{
	CartesianProd<uint> leafs_prod;
	for (const auto& i : vindex.vect()) {
		leafs_prod.incSize();
		for (uint s : i.ind->rules.at(r).leafs) {
			leafs_prod.incDim(s);
		}
	}
	if (leafs_prod.card() == 0) {
		return;
	}
	while (true) {
		vector<uint> leafs = leafs_prod.data();
		if (!restrictions || restrictions->count(leafs)) {
			unif[leafs];
			terms[leafs] = LightTree(r, {});
		}
		if (!leafs_prod.hasNext()) {
			break;
		}
		leafs_prod.makeNext();
	}
}

struct MIndexSpace {
	map<LightSymbol, set<uint>> vars;
	map<LightSymbol, set<uint>> consts;
	map<const Rule*, set<uint>> rules;
	CartesianProd<LightSymbol> vars_prod;
	uint active_size = 0;
};

MIndexSpace prepare_space(const VectorIndex& vindex) {
	MIndexSpace space;
	for (uint i = 0; i < vindex.size(); ++ i) {
		space.vars_prod.incSize();
		VectorIndex::IndexPtr ptrs = vindex.vect()[i];
		if (ptrs.ind->size == 0) {
			space.vars_prod.skip(i);
		} else {
			++ space.active_size;
			for (const auto& p : ptrs.ind->vars) {
				if (p.first.rep) {
					space.vars[p.first].insert(i);
					space.vars_prod.incDim(p.first);
				} else {
					space.consts[p.first].insert(i);
				}
			}
			for (const auto& p : ptrs.ind->rules) {
				space.rules[p.first].insert(i);
			}
		}
	}
	return space;
}

void unify_variables(const VectorIndex& vindex, MultyUnifiedSubs& unif, MultyUnifiedTerms& terms, const Restrictions* restrictions, const MIndexSpace& space)
{
	for (auto p : space.vars) {
		LightSymbol v = p.first;
		CartesianProd<LightSymbol> vars_prod = space.vars_prod;
		for (uint i : p.second) {
			vars_prod.fix(i, v);
		}
		if (vars_prod.card() > 0) {
			while (true) {
				vector<LightSymbol> w = vars_prod.data();
				unify_vars_step(vindex, w, LightTree(v), unif, terms, restrictions);
				if (!vars_prod.hasNext()) {
					break;
				}
				vars_prod.makeNext();
			}
		} else if (p.second.size() == space.active_size) {
			// All indexes have variable 'v'
			unify_const_step(vindex, v, unif, terms, restrictions);
		}
	}
}

void unify_consts(const VectorIndex& vindex, MultyUnifiedSubs& unif, MultyUnifiedTerms& terms, const Restrictions* restrictions, const MIndexSpace& space)
{
	for (auto p : space.consts) {
		set<uint> consts_part = p.second;
		LightSymbol c = p.first;
		CartesianProd<LightSymbol> vars_prod = space.vars_prod;
		for (uint i : p.second) {
			vars_prod.skip(i);
		}
		if (vars_prod.card() > 0) {
			while (true) {
				vector<LightSymbol> w = vars_prod.data();
				CartesianProd<uint> const_leafs_prod;
				for (uint i = 0; i < vindex.size(); ++ i) {
					const_leafs_prod.incSize();
					if (consts_part.count(i)) {
						for (uint s : vindex.index(i)->vars.at(c)) {
							const_leafs_prod.incDim(s);
						}
					} else {
						const_leafs_prod.skip(i);
					}
				}
				if (const_leafs_prod.card() > 0) {
					while (true) {
						vector<uint> leafs = const_leafs_prod.data();
						if (!restrictions || restrictions->count(leafs)) {
							unify_vars_step(
								vindex, w,
								LightTree(c),
								unif, terms,
								restrictions, leafs, consts_part
							);
						}
						if (!const_leafs_prod.hasNext()) {
							break;
						}
						const_leafs_prod.makeNext();
					}
				}
				if (!vars_prod.hasNext()) {
					break;
				}
				vars_prod.makeNext();
			}
		} else if (p.second.size() == space.active_size) {
			// All indexes have constant 'c'
			unify_const_step(vindex, c, unif, terms, restrictions);
		}
	}
}

void unify_branch_rule(const VectorIndex& vindex, const Rule* r, MultyUnifiedSubs& unif, MultyUnifiedTerms& terms, const Restrictions* restrictions, const MIndexSpace& space)
{
	vector<MultyUnifiedTerms> ch(r->arity());
	VectorIndex x;
	for (const auto& ptrs : vindex.vect()) {
		if (ptrs.ind->rules.count(r)) {
			x.add(ptrs.ind->rules.at(r).child[0].get(), ptrs.values);
		} else {
			cout << "XXX" << endl;
		}
	}
	ch[0] = unify(x, unif, restrictions);
	Restrictions common;
	for (const auto& p : ch[0]) {
		common.insert(p.first);
	}
	for (uint i = 1; i < r->arity(); ++ i) {
		for (const auto& ptrs : vindex.vect()) {
			if (ptrs.ind->rules.count(r)) {
				x.add(ptrs.ind->rules.at(r).child[i].get(), ptrs.values);
			} else {
				cout << "YYY" << endl;
			}
		}
		ch[i] = unify(x, unif, &common);
		common.clear();
		for (const auto& p : ch[i]) {
			common.insert(p.first);
		}
	}
	for (const auto& c : common) {
		LightTree::Children childern;
		for (uint i = 0; i < r->arity(); ++ i) {
			childern.push_back(make_unique<LightTree>(ch[i][c]));
		}
		terms[c] = LightTree(r, childern);
	}
}


void unify_rules(const VectorIndex& vindex, MultyUnifiedSubs& unif, MultyUnifiedTerms& terms, const Restrictions* restrictions, const MIndexSpace& space)
{
	for (auto p : space.rules) {
		const Rule* r = p.first;
		set<uint> rules_part = p.second;
		set<uint> vars_part = complement(rules_part, vindex.size());
		CartesianProd<LightSymbol> vars_prod = space.vars_prod;
		for (uint i : p.second) {
			vars_prod.skip(i);
		}
		if (vars_prod.card() > 0) {
			while (true) {
				vector<LightSymbol> w = vars_prod.data();
				if (r->arity() == 0) {
					CartesianProd<uint> leafs_prod;
					for (uint i = 0; i < vindex.size(); ++ i) {
						leafs_prod.incSize();
						if (rules_part.count(i)) {
							for (uint s : vindex.index(i)->rules.at(r).leafs) {
								leafs_prod.incDim(s);
							}
						} else {
							leafs_prod.skip(i);
						}
					}
					if (leafs_prod.card() > 0) {
						while (true) {
							vector<uint> leafs = leafs_prod.data();
							if (!restrictions || restrictions->count(leafs)) {
								unify_vars_step(
									vindex, w,
									LightTree(r, {}),
									unif, terms,
									restrictions, leafs, rules_part
								);
							}
							if (!leafs_prod.hasNext()) {
								break;
							}
							leafs_prod.makeNext();
						}
					}
				} else {
					vector<MultyUnifiedTerms> child_terms(r->arity());
					for (uint i = 0; i < r->arity(); ++ i) {
						VectorIndex child_vindex;
						for (uint j = 0; j < vindex.size(); ++ j) {
							if (rules_part.count(j)) {
								if (!vindex.index(j)->rules.count(r)) {
									cout << "i = " << i << endl;
									cout << "rules_part = " << show(rules_part) << endl;
								}
								child_vindex.add(vindex.index(j)->rules.at(r).child[i].get(), vindex.values(j));
							}
						}
						MultyUnifiedSubs unif1 = reduce_subs(unif, rules_part);
						for (const auto& p : unify(child_vindex, unif1, restrictions)) {
							vector<uint> leafs = p.first;
							LightTree::Children children(r->arity());
							children.push_back(make_unique<LightTree>(p.second));
							for (uint i = 1; i < r->arity(); ++ i) {
								if (child_terms[i].count(leafs)) {
									const LightTree& ch = child_terms[i].at(leafs);
									children.push_back(make_unique<LightTree>(ch));
								} else {
									break;
								}
							}
							if (children.size() == r->arity()) {
								unify_vars_step(
									vindex, w,
									LightTree(r, children),
									unif, terms,
									restrictions, leafs, rules_part, unif1[leafs]
								);
							}
						}
					}
				}
				if (!vars_prod.hasNext()) {
					break;
				}
				vars_prod.makeNext();
			}
		} else if (p.second.size() == space.active_size) {
			if (r->arity() == 0) {
				// All indexes have zero-ary rule 'r'
				unify_rule_step(vindex, r, unif, terms, restrictions);
			} else {
				unify_branch_rule(vindex, r, unif, terms, restrictions, space);
			}
		}
	}
}

MultyUnifiedTerms unify(const VectorIndex& vindex, MultyUnifiedSubs& unif, const Restrictions* restrictions)
{
	MultyUnifiedTerms terms;
	MIndexSpace space = prepare_space(vindex);

	unify_variables(vindex, unif, terms, restrictions, space);
	unify_consts(vindex, unif, terms, restrictions, space);
	unify_rules(vindex, unif, terms, restrictions, space);

	return terms;
}

}}}


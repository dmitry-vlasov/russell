#include "rus_prover_cartesian.hpp"
#include "rus_prover_unify.hpp"
#include "rus_prover_multy_index.hpp"

namespace mdl { namespace rus { namespace prover {

string show(const vector<const Index*>& mindex) {
	string ret;
	for (uint i = 0; i < mindex.size(); ++ i) {
		ret += "index: " + to_string(i) + "\n";
		ret += mindex[i]->show() + "\n";
		ret += "-----------------------------\n\n";
	}
	return ret;
}

string show(const set<uint>& s) {
	string ret;
	ret += "{";
	for (uint i : s) {
		ret += to_string(i) + ", ";
	}
	ret += "}";
	return ret;
}

set<uint> complement(const set<uint>& s, uint m) {
	set<uint> ret;
	for (uint i = 0; i < m; ++ i) {
		if (!s.count(i)) {
			ret.insert(i);
		}
	}
	return ret;
}

bool are_complement(const set<uint>& s1, set<uint>& s2, uint m) {
	for (uint i = 0; i < m; ++ i) {
		if (s1.count(i) + s2.count(i) != 1) {
			return false;
		}
	}
	return true;
}

vector<uint> reduce_leafs(const vector<uint>& leafs, const set<uint>& s) {
	vector<uint> ret;
	for (uint i = 0 ; i < leafs.size(); ++ i) {
		if (s.count(i)) {
			ret.push_back(leafs[i]);
		}
	}
	return ret;
}

vector<uint> join_leafs(const vector<uint>& leafs1,const vector<uint>& leafs2, const set<uint>& s) {
	vector<uint> ret;
	for (uint i = 0, n = 0, m = 0 ; i < leafs1.size() + leafs2.size(); ++ i) {
		if (s.count(i)) {
			ret.push_back(leafs1[n++]);
		} else {
			ret.push_back(leafs2[m++]);
		}
	}
	return ret;
}

MultyUnifiedSubs reduce_subs(const MultyUnifiedSubs& subs, const set<uint>& s) {
	MultyUnifiedSubs ret;
	for (const auto& p : subs) {
		ret[reduce_leafs(p.first, s)] = p.second;
	}
	return ret;
}

Restrictions reduce_restrictions(const Restrictions& restrictions, const set<uint>& s) {
	Restrictions ret;
	for (const auto& leafs : restrictions) {
		ret.insert(reduce_leafs(leafs, s));
	}
	return ret;
}


void unify_vars_step(
	const vector<const Index*>& mindex,
	const vector<LightSymbol>& w,
	LightTree t,
	MultyUnifiedSubs& unif,
	MultyUnifiedTerms& terms,
	const set<vector<uint>>* restrictions,
	const vector<uint>& other_leafs = vector<uint>(),
	const set<uint>& other_indexes = set<uint>(),
	const Subst& other_subst = Subst())
{
	CartesianProduct<uint> leafs_prod;
	for (uint i = 0; i < w.size(); ++ i) {
		leafs_prod.incSize();
		if (!other_indexes.count(i)) {
			if (mindex[i]->vars.count(w[i])) {
				for (uint s : mindex[i]->vars.at(w[i])) {
					leafs_prod.incDim(s);
				}
			} else {
				cout << "AAA: " << i << endl;
				for (auto s : w) {
					cout << show(s) << " ";
				}
				cout << endl << show(w[i]) << endl;
				cout << show(mindex) << endl;
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
	const vector<const Index*>& mindex,
	LightSymbol c,
	MultyUnifiedSubs& unif,
	MultyUnifiedTerms& terms,
	const set<vector<uint>>* restrictions)
{
	CartesianProduct<uint> leafs_prod;
	for (uint i = 0; i < mindex.size(); ++ i) {
		leafs_prod.incSize();
		if (!mindex[i]->vars.count(c)) {
				cout << "BBB" << endl;
			}
		for (uint s : mindex[i]->vars.at(c)) {
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
	const vector<const Index*>& mindex,
	const rus::Rule* r,
	MultyUnifiedSubs& unif,
	MultyUnifiedTerms& terms,
	const set<vector<uint>>* restrictions)
{
	CartesianProduct<uint> leafs_prod;
	for (uint i = 0; i < mindex.size(); ++ i) {
		leafs_prod.incSize();
		if (!mindex[i]->rules.count(r)) {
				cout << "CCC" << endl;
			}
		for (uint s : mindex[i]->rules.at(r).leafs) {
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
	CartesianProduct<LightSymbol> vars_prod;
};

MIndexSpace prepare_space(const vector<const Index*>& mindex) {
	MIndexSpace space;
	for (uint i = 0; i < mindex.size(); ++ i) {
		space.vars_prod.incSize();
		for (const auto& p : mindex[i]->vars) {
			if (p.first.rep) {
				space.vars[p.first].insert(i);
				space.vars_prod.incDim(p.first);
			} else {
				space.consts[p.first].insert(i);
			}
		}
		for (const auto& p : mindex[i]->rules) {
			space.rules[p.first].insert(i);
		}
	}
	return space;
}

void unify_variables(const vector<const Index*>& mindex, MultyUnifiedSubs& unif, MultyUnifiedTerms& terms, const Restrictions* restrictions, MIndexSpace& space)
{
	for (auto p : space.vars) {
		LightSymbol v = p.first;
		space.vars_prod.reset();
		for (uint i : p.second) {
			space.vars_prod.fix(i, v);
		}
		while (true) {
			vector<LightSymbol> w = space.vars_prod.data();
			unify_vars_step(mindex, w, LightTree(v), unif, terms, restrictions);
			if (!space.vars_prod.hasNext()) {
				break;
			}
			space.vars_prod.makeNext();
		}
	}
}

void unify_consts(const vector<const Index*>& mindex, MultyUnifiedSubs& unif, MultyUnifiedTerms& terms, const Restrictions* restrictions, MIndexSpace& space)
{
	for (auto p : space.consts) {
		set<uint> consts_part = p.second;
		LightSymbol c = p.first;
		space.vars_prod.reset();
		for (uint i : p.second) {
			space.vars_prod.skip(i);
		}
		if (space.vars_prod.card() > 0) {
			while (true) {
				vector<LightSymbol> w = space.vars_prod.data();

				CartesianProduct<uint> const_leafs_prod;
				for (uint i = 0; i < mindex.size(); ++ i) {
					const_leafs_prod.incSize();
					if (consts_part.count(i)) {
						for (uint s : mindex[i]->vars.at(c)) {
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
								mindex, w,
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
				if (!space.vars_prod.hasNext()) {
					break;
				}
				space.vars_prod.makeNext();
			}
		} else if (p.second.size() == mindex.size()) {
			// All indexes have constant 'c'
			unify_const_step(mindex, c, unif, terms, restrictions);
		}
	}
}

void unify_branch_rule(const vector<const Index*>& mindex, const Rule* r, MultyUnifiedSubs& unif, MultyUnifiedTerms& terms, const Restrictions* restrictions, MIndexSpace& space)
{
	vector<MultyUnifiedTerms> ch(r->arity());
	vector<const Index*> x;
	for (auto ind : mindex) {
		if (ind->rules.count(r)) {
			x.push_back(ind->rules.at(r).child[0].get());
		} else {
			cout << "XXX" << endl;
			return;
		}
	}
	ch[0] = unify(x, unif, restrictions);
	Restrictions common;
	for (const auto& p : ch[0]) {
		common.insert(p.first);
	}
	for (uint i = 1; i < r->arity(); ++ i) {
		vector<const Index*> x;
		for (auto ind : mindex) {
			if (ind->rules.count(r)) {
				x.push_back(ind->rules.at(r).child[i].get());
			} else {
				cout << "YYY" << endl;
				return;
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


void unify_rules(const vector<const Index*>& mindex, MultyUnifiedSubs& unif, MultyUnifiedTerms& terms, const Restrictions* restrictions, MIndexSpace& space)
{
	for (auto p : space.rules) {
		const Rule* r = p.first;
		set<uint> rules_part = p.second;
		set<uint> vars_part = complement(rules_part, mindex.size());
		space.vars_prod.reset();
		for (uint i : p.second) {
			space.vars_prod.skip(i);
		}
		if (space.vars_prod.card() > 0) {
			while (true) {
				vector<LightSymbol> w = space.vars_prod.data();
				if (r->arity() == 0) {
					CartesianProduct<uint> leafs_prod;
					for (uint i = 0; i < mindex.size(); ++ i) {
						leafs_prod.incSize();
						if (rules_part.count(i)) {
							for (uint s : mindex[i]->rules.at(r).leafs) {
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
									mindex, w,
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
						vector<const Index*> child_mindex;
						for (uint j = 0; j < mindex.size(); ++ j) {
							if (rules_part.count(j)) {
								if (!mindex[j]->rules.count(r)) {
									cout << "i = " << i << endl;
									cout << "rules_part = " << show(rules_part) << endl;
								}
								child_mindex.push_back(mindex[j]->rules.at(r).child[i].get());
							}
						}
						MultyUnifiedSubs unif1 = reduce_subs(unif, rules_part);
						for (const auto& p : unify(child_mindex, unif1, restrictions)) {
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
									mindex, w,
									LightTree(r, children),
									unif, terms,
									restrictions, leafs, rules_part, unif1[leafs]
								);
							}
						}
					}
				}
				if (!space.vars_prod.hasNext()) {
					break;
				}
				space.vars_prod.makeNext();
			}
		} else if (p.second.size() == mindex.size()) {
			if (r->arity() == 0) {
				// All indexes have zero-ary rule 'r'
				unify_rule_step(mindex, r, unif, terms, restrictions);
			} else {
				unify_branch_rule(mindex, r, unif, terms, restrictions, space);
			}
		}
	}
}

MultyUnifiedTerms unify(const vector<const Index*>& mindex, MultyUnifiedSubs& unif, const Restrictions* restrictions)
{
	static int c = 0;
	cout << "MULTY INDEX: " << ++c << endl;
	cout << show(mindex) << endl;

	MultyUnifiedTerms terms;
	MIndexSpace space = prepare_space(mindex);

	if (space.vars_prod.card() > 0) {
		unify_variables(mindex, unif, terms, restrictions, space);
	}
	unify_consts(mindex, unif, terms, restrictions, space);
	unify_rules(mindex, unif, terms, restrictions, space);

	return terms;
}

}}}


#include "rus_prover_cartesian.hpp"
#include "rus_prover_unify.hpp"
#include "rus_prover_multy_index.hpp"

namespace mdl { namespace rus { namespace prover {

void unify_vars_step(
	const vector<const Index*>& mindex,
	const vector<LightSymbol>& w,
	LightTree t,
	MultyUnifiedSubs& unif,
	MultyUnifiedTerms& terms,
	const set<vector<uint>>* restrictions)
{
	CartesianProduct<uint> leafs_prod;
	for (uint i = 0; i < mindex.size(); ++ i) {
		for (uint s : mindex.at(i)->vars.at(w[i])) {
			leafs_prod.incDim(s);
		}
		leafs_prod.incSize();
	}
	if (leafs_prod.card() == 0) {
		return;
	}
	while (true) {
		vector<uint> leafs = leafs_prod.data();
		if (!restrictions || restrictions->count(leafs)) {
			LightTree unified = unify_step(unif[leafs], w, t);
			if (!unified.empty()) {
				if (terms.count(leafs)) {
					cout << "MULTIPLE UNIFICATION RESULTS" << endl;
					cout << "try_variable_replacement" << endl;
				}
				terms[leafs] = unified;
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
		for (uint s : mindex.at(i)->vars.at(c)) {
			leafs_prod.incDim(s);
		}
		leafs_prod.incSize();
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
		for (uint s : mindex.at(i)->rules.at(r).leafs) {
			leafs_prod.incDim(s);
		}
		leafs_prod.incSize();
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
		space.vars_prod.incSize();
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
		LightSymbol c = p.first;
		space.vars_prod.reset();
		for (uint i : p.second) {
			space.vars_prod.skip(i);
		}
		if (space.vars_prod.card() > 0) {
			while (true) {
				vector<LightSymbol> w = space.vars_prod.data();
				unify_vars_step(mindex, w, LightTree(c), unif, terms, restrictions);
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

void unify_rules(const vector<const Index*>& mindex, MultyUnifiedSubs& unif, MultyUnifiedTerms& terms, const Restrictions* restrictions, MIndexSpace& space)
{
	for (auto p : space.rules) {
		const Rule* r = p.first;
		space.vars_prod.reset();
		for (uint i : p.second) {
			space.vars_prod.skip(i);
		}
		if (r->arity() == 0) {
			if (space.vars_prod.card() > 0) {
				while (true) {
					vector<LightSymbol> w = space.vars_prod.data();
					unify_vars_step(mindex, w, LightTree(r, {}), unif, terms, restrictions);
					if (!space.vars_prod.hasNext()) {
						break;
					}
					space.vars_prod.makeNext();
				}
			} else if (p.second.size() == mindex.size()) {
				// All indexes have zero-ary rule 'r'
				unify_rule_step(mindex, r, unif, terms, restrictions);
			}
		} else {
			vector<MultyUnifiedTerms> ch(r->arity());
			vector<const Index*> x;
			for (auto ind : mindex) {
				if (ind->rules.count(r)) {
					x.push_back(ind->rules.at(r).child[0].get());
				} else {

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
					if (!ind->rules.count(r)) {
						cout << "EEE" << endl;
					}
					x.push_back(ind->rules.at(r).child[i].get());
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
	}
}

MultyUnifiedTerms unify(const vector<const Index*>& mindex, MultyUnifiedSubs& unif, const Restrictions* restrictions)
{
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


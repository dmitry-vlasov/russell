#include "rus_prover_cartesian.hpp"
#include "rus_prover_unify.hpp"
#include "rus_prover_multy_index.hpp"

namespace mdl { namespace rus { namespace prover {

void unify_step(
	const vector<const Index*>& mindex,
	const vector<LightSymbol>& w,
	LightTree t,
	MultyIndex::UnifiedSubs& unif,
	MultyIndex::UnifiedTerms& terms,
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

void unify(
	const vector<const Index*>& mindex,
	MultyIndex::UnifiedSubs& unif,
	MultyIndex::UnifiedTerms& terms,
	const set<vector<uint>>* restrictions = nullptr)
{
	map<LightSymbol, set<uint>> vars;
	map<LightSymbol, set<uint>> consts;
	map<const Rule*, set<uint>> rules;

	CartesianProduct<LightSymbol> vars_prod;

	for (uint i = 0; i < mindex.size(); ++ i) {
		for (const auto& p : mindex[i]->vars) {
			if (p.first.rep) {
				vars[p.first].insert(i);
				vars_prod.incDim(p.first);
			} else {
				consts[p.first].insert(i);
			}
		}
		for (const auto& p : mindex[i]->rules) {
			rules[p.first].insert(i);
		}
		vars_prod.incSize();
	}

	for (auto p : vars) {
		LightSymbol v = p.first;
		vars_prod.reset();
		for (uint i : p.second) {
			vars_prod.fix(i, v);
		}
		if (vars_prod.card() > 0) {
			while (true) {
				vector<LightSymbol> w = vars_prod.data();
				unify_step(mindex, w, LightTree(v), unif, terms, restrictions);
				if (!vars_prod.hasNext()) {
					break;
				}
				vars_prod.makeNext();
			}
		}
	}
	for (auto p : consts) {
		LightSymbol c = p.first;
		vars_prod.reset();
		for (uint i : p.second) {
			vars_prod.skip(i);
		}
		if (vars_prod.card() > 0) {
			while (true) {
				vector<LightSymbol> w = vars_prod.data();
				unify_step(mindex, w, LightTree(c), unif, terms, restrictions);
				if (!vars_prod.hasNext()) {
					break;
				}
				vars_prod.makeNext();
			}
		}
	}
	for (auto p : rules) {
		const Rule* r = p.first;
		vars_prod.reset();
		for (uint i : p.second) {
			vars_prod.skip(i);
		}
		if (r->arity() == 0) {
			if (vars_prod.card() > 0) {
				while (true) {
					vector<LightSymbol> w = vars_prod.data();
					unify_step(mindex, w, LightTree(r, {}), unif, terms, restrictions);
					if (!vars_prod.hasNext()) {
						break;
					}
					vars_prod.makeNext();
				}
			}
		} else {
			vector<MultyIndex::UnifiedTerms> ch(r->arity());
			vector<const Index*> x;
			for (auto ind : mindex) {
				x.push_back(ind->rules.at(r).child[0].get());
			}
			unify(x, unif, ch[0], restrictions);
			set<vector<uint>> common;
			for (const auto& p : ch[0]) {
				common.insert(p.first);
			}
			for (uint i = 1; i < r->arity(); ++ i) {
				vector<const Index*> x;
				for (auto ind : mindex) {
					x.push_back(ind->rules.at(r).child[i].get());
				}
				unify(x, unif, ch[i], &common);
				common.clear();
				for (const auto& p : ch[0]) {
					common.insert(p.first);
				}
			}
		}
	}
}

}}}


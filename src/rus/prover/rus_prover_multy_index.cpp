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

void unify_branch_rule(const vector<const Index*>& mindex, const Rule* r, MultyUnifiedSubs& unif, MultyUnifiedTerms& terms, const Restrictions* restrictions, MIndexSpace& space)
{
	vector<MultyUnifiedTerms> ch(r->arity());
	vector<const Index*> x;
	for (auto ind : mindex) {
		if (ind->rules.count(r)) {
			x.push_back(ind->rules.at(r).child[0].get());
		} else {
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

/*
static void gather(const Rule* r, MultyUnifiedTerms& u, MultyUnifiedTerms w[], uint sz, const Restrictions* restrictions) {
	for (auto& p : w[0]) {
		uint d = p.first;
		LightTree::Children ch;
		ch.push_back(make_unique<LightTree>(p.second));
		int i = 1;
		for (; i < sz; ++ i) {
			assert(w[i].count(d));
			ch.emplace_back(make_unique<LightTree>(w[i][d]));
		}
		u[d] = LightTree(r, ch);
	}
}

static MultyUnifiedTerms gather_terms(const vector<const Index*> i, const Restrictions* restrictions);

static MultyUnifiedTerms gather_terms(const Rule* r, const vector<const Index::Node*>& n, const Restrictions* restrictions) {
	MultyUnifiedTerms ret;
	MultyUnifiedTerms un[n.child.size()];
	for (uint d : n.leafs) {
		ret[d] = LightTree(r, LightTree::Children());
	}
	int c = 0;
	for (const auto& i : n.child) {
		un[c++] = gather_terms(i.get());
	}
	if (c > 0) {
		gather(r, ret, un, c);
	}
	return ret;
}

static MultyUnifiedTerms gather_terms(const vector<const Index*>, const Restrictions* restrictions) {
	MultyUnifiedTerms ret;
	for (const auto& p : i->vars) {
		for (uint d : p.second) {
			ret[d] = LightTree(p.first);
		}
	}
	for (const auto& p : i->rules) {
		for (auto& q : gather_terms(p.first, p.second)) {
			ret.emplace(q.first, q.second);
		}
	}
	return ret;
}

static MultyUnifiedTerms gather_terms(const Rule* r, const MIndexSpace& space, const vector<const Index*> mindex, const Restrictions* restrictions) {
	MultyUnifiedTerms ret;
	vector<const Index::Node*> mnode;
	for (uint i = 0; i < mindex.size(); ++ i) {
		if (space.vars_prod.get(i).kind == CartesianIter::Dim::NORM) {
			mnode.push_back(mindex[i]->rules.at(r));
		} else {
			mnode.push_back(nullptr);
		}
	}


	for (const auto& p : i->vars) {
		for (uint d : p.second) {
			ret[d] = LightTree(p.first);
		}
	}
	for (const auto& p : i->rules) {
		for (auto& q : gather_terms(p.first, p.second)) {
			ret.emplace(q.first, q.second);
		}
	}
	return ret;
}
*/
void unify_rules(const vector<const Index*>& mindex, MultyUnifiedSubs& unif, MultyUnifiedTerms& terms, const Restrictions* restrictions, MIndexSpace& space)
{
	for (auto p : space.rules) {
		const Rule* r = p.first;
		space.vars_prod.reset();
		for (uint i : p.second) {
			space.vars_prod.skip(i);
		}
		if (space.vars_prod.card() > 0) {
			while (true) {
				vector<LightSymbol> w = space.vars_prod.data();
				if (r->arity() == 0) {
					unify_vars_step(mindex, w, LightTree(r, {}), unif, terms, restrictions);
				} else {
					//for (const auto& q : gather_terms(r, space, mindex, restrictions)) {
					//	unify_vars_step(mindex, w, q, unif, terms, restrictions);
					//}
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


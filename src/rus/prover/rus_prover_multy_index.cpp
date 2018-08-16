#include "rus_prover_cartesian.hpp"
#include "rus_prover_unify.hpp"
#include "rus_prover_multy_index.hpp"

namespace mdl { namespace rus { namespace prover {

void try_variable_replacement(const vector<Index*>& mindex, LightSymbol v, const vector<LightSymbol>& w, MultyIndex::UnifiedSubs& unif, MultyIndex::UnifiedTerms& ret) {
	CartesianProduct<uint> leafs_prod;
	for (uint i = 0; i < mindex.size(); ++ i) {
		for (uint s : mindex[i]->vars[w[i]]) {
			leafs_prod.incDim(s);
		}
		leafs_prod.incSize();
	}
	while (true) {
		vector<uint> leafs = leafs_prod.data();
		LightTree unified = unify_step(unif[leafs], w, LightTree(v));
		if (!unified.empty()) {
			if (ret.count(leafs)) {
				cout << "MULTIPLE UNIFICATION RESULTS" << endl;
				cout << "try_variable_replacement" << endl;
			}
			ret[leafs] = unified;
		}
		if (!leafs_prod.hasNext()) {
			break;
		}
		leafs_prod.makeNext();
	}
}

MultyIndex::UnifiedTerms unify(const vector<Index*>& mindex, MultyIndex::UnifiedSubs& unif) {
	MultyIndex::UnifiedTerms ret;

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
		while (true) {
			vector<LightSymbol> w = vars_prod.data();
			try_variable_replacement(mindex, v, w, unif, ret);
			if (!vars_prod.hasNext()) {
				break;
			}
			vars_prod.makeNext();
		}
	}




/*
	for (const auto& p : index->vars) {
		LightSymbol iv = p.first;
		for (uint d : p.second) {
			if (iv.rep) {
				if (debug_index && d == 0) {
					debug_unify = true;
					cout << "UNIF A:" << endl;
					cout << show(unif[d]) << endl;
					cout << "iv: " << show(iv) << endl;
				}
				ret[d] = try_to_expand_subst(unif[d], iv, t);
				debug_unify = false;
			} else {
				if (t.kind() == LightTree::VAR) {
					if (t.var().rep) {
						if (debug_index && d == 0) {
							//debug_unify = true;
							cout << "UNIF B:" << endl;
							cout << show(unif[d]) << endl;
						}
						ret[d] = try_to_expand_subst(unif[d], t.var(), LightTree(iv));
						//debug_unify = false;
					} else if (iv == t.var()) {
						unif[d];
						ret[d] = LightTree(iv);
					}
				}
			}
		}
	}
	if (t.kind() == LightTree::VAR) {
		LightSymbol tv = t.var();
		if (tv.rep) {
			for (const auto& p : index->rules) {
				const Rule* r = p.first;
				const Index::Node& n = p.second;
				for (const auto& q : gather_terms(r, n)) {
					if (debug_index && q.first == 3) {
						//debug_unify = true;
						cout << "UNIF C:" << endl;
						cout << show(unif[q.first]) << endl;
					}
					ret[q.first] = try_to_expand_subst(unif[q.first], tv, q.second);
				}
			}
		}
	}
	if (t.kind() == LightTree::NODE && index->rules.count(t.rule())) {
		const Index::Node& n = index->rules.at(t.rule());
		if (n.is_leaf()) {
			for (uint d : n.leafs) {
				unif[d];
				ret[d] = LightTree(t.rule(), {});
			}
		} else {
			auto ch = t.children().begin();
			vector<UnifiedTerms> un;
			for (const auto& i : n.child) {
				un.push_back(unify(i.get(), *(ch++)->get(), unif));
			}
			for (const auto& p : un[0]) {
				uint d = p.first;
				LightTree::Children ch;
				for (auto& u : un) {
					if (!u[d].empty()) {
						ch.push_back(make_unique<LightTree>(u[d]));
					} else {
						break;
					}
				}
				if (ch.size() == n.child.size()) {
					ret[d] = apply(unif[d], LightTree(t.rule(), ch));
				}
			}
		}
	}*/
	return ret;
}

}}}


#include "rus_prover_cartesian.hpp"
#include "rus_prover_multy_index.hpp"

namespace mdl { namespace rus { namespace prover {

/*

LightTree try_to_expand_subst(Subst& unif, LightSymbol v, LightTree t) {
	if (!(*v.type <= *t.type())) {
		return LightTree();
	}
	LightTree t_substituted = apply(unif, t);
	vector<LightTree> to_unify({t_substituted});
	if (unif.maps(v)) {
		to_unify.push_back(unif.sub[v]);
	}
	if (to_unify.size() > 1) {
		Subst un;
		LightTree t = unify(to_unify, un);
		if (!t.empty()) {
			LightTree term =
				(v.type == t.type()) ?
				t :
				LightTree(find_super(t.type(), v.type), new LightTree(t));

			if (debug_ind) {
				cout << "AAA UNIF:" << endl;
				cout << Indent::paragraph(show(unif)) << endl;
				cout << "var: " << show(v) << endl;
				cout << "term: " << show(term) << endl;
			}
			if (unif.compose(un)) {
				if (debug_ind) {
					cout << "AAA SUCCESS:" << endl << endl;
				}
				return term;
			} else {
				if (debug_ind) {
					cout << "AAA FAILURE:" << endl << endl;
				}
			}
		} else {
			if (debug_ind) {
				cout << "XXX FAILURE:" << endl << endl;
			}
		}
	} else {
		LightTree term =
			(v.type == t_substituted.type()) ?
			t_substituted :
			LightTree(find_super(t_substituted.type(), v.type), new LightTree(t_substituted));

		if (debug_ind) {
			cout << "BBB UNIF:" << endl;
			cout << Indent::paragraph(show(unif)) << endl;
			cout << "var: " << show(v) << endl;
			cout << "term: " << show(term) << endl;
		}

		if (unif.compose(Subst(v, term))) {

			if (debug_ind) {
				cout << "BBB SUCCESS:" << endl << endl;
			}

			return term;
		} else {
			if (debug_ind) {
				cout << "BBB FAILURE:" << endl << endl;
			}
		}
	}
	return LightTree();
}
*/

MultyIndex::UnifiedTerms unify(const vector<Index*>& mindex, MultyIndex::UnifiedSubs& unif) {
	MultyIndex::UnifiedTerms ret;

	map<LightSymbol, set<uint>> vars;
	map<LightSymbol, set<uint>> consts;
	map<const Rule*, set<uint>> rules;

	CartesianMap<LightSymbol> vars_map;

	for (uint i = 0; i < mindex.size(); ++ i) {
		for (const auto& p : mindex[i]->vars) {
			if (p.first.rep) {
				vars[p.first].insert(i);
				vars_map.incDim(p.first);
			} else {
				consts[p.first].insert(i);
			}
		}
		for (const auto& p : mindex[i]->rules) {
			rules[p.first].insert(i);
		}
		vars_map.incSize();
	}

	for (auto p : vars) {
		LightSymbol v = p.first;
		vars_map.reset();
		for (uint i : vars[v]) {
			vars_map.fix(i, v);
		}
		while (true) {

			if (!vars_map.hasNext()) {
				break;
			}
			vars_map.makeNext();
		}
		for (uint i : vars[v]) {
			vars_map.fix(i, v);
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


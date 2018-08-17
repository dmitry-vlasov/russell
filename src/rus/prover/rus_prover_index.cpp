#include "rus_prover_index.hpp"
#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

static void intersect_show(map<uint, vector<string>>& u, map<uint, string> w[], uint sz) {
	for (auto p : w[0]) {
		uint d = p.first;
		vector<string> vstr;
		int i = 0;
		for (; i < sz; ++ i) {
			if (!w[i].count(d)) {
				break;
			} else {
				vstr.push_back(w[i][d]);
			}
		}
		if (i == sz) {
			u[d] = vstr;
		}
	}
}

static map<uint, string> showVector(const Index* index) {
	map<uint, string> ret;
	for (const auto& p : index->vars) {
		for (const auto& d : p.second) {
			ret[d] = rus::prover::show(p.first);
		}
	}
	for (const auto& p : index->rules) {
		const Rule* r = p.first;
		if (!p.second.child.size()) {
			for (const auto& d : p.second.leafs) {
				ret[d] = rus::show(r->term);
			}
		} else {
			const vector<unique_ptr<Index>>& ch = p.second.child;
			map<uint, string> show_ch[ch.size()];
			int c = 0;
			for (auto& ind : ch) {
				 show_ch[c++] = showVector(ind.get());
			}
			map<uint, vector<string>> intersected;
			if (c > 0) {
				intersect_show(intersected, show_ch, c);
			}
			for (auto pr : intersected) {
				string str;
				int x = 0;
				for (auto s : r->term.symbols) {
					if (s.kind() == Symbol::VAR) {
						str += pr.second[x++];
					} else {
						str += rus::show(s);
					}
				}
				ret[pr.first] = str;
			}
		}
	}
	return ret;
}

static void add_to_index(Index* index, const LightTree& t, uint s) {
	if (t.kind() == LightTree::VAR) {
		index->vars[t.var()].insert(s);
	} else {
		if (!t.children().size()) {
			index->rules[t.rule()].leafs.insert(s);
		} else {
			bool is_new = !index->rules.count(t.rule());
			vector<unique_ptr<Index>>& ch = index->rules[t.rule()].child;
			if (is_new) {
				for (const auto& c : t.children()) {
					ch.push_back(make_unique<Index>());
				}
			}
			auto i = ch.begin();
			for (const auto& c : t.children()) {
				add_to_index((i++)->get(), *c.get(), s);
			}
		}
	}
}

typedef map<uint, LightTree> UnifiedTerms;

static UnifiedTerms gather_terms(const Index& i);

static UnifiedTerms gather_terms(const Rule* r, const Index::Node& n) {
	UnifiedTerms ret;
	for (uint d : n.leafs) {
		ret[d] = LightTree(r, {});
	}
	vector<UnifiedTerms> un;
	for (uint i = 0; i < n.child.size(); ++ i) {
		un.push_back(gather_terms(*n.child[i]));
	}
	if (un.size() > 0) {
		for (auto& p : un[0]) {
			uint d = p.first;
			LightTree::Children ch;
			ch.push_back(make_unique<LightTree>(p.second));
			for (int i = 1; i < un.size(); ++ i) {
				assert(un.at(i).count(d));
				ch.emplace_back(make_unique<LightTree>(un.at(i).at(d)));
			}
			ret[d] = LightTree(r, ch);
		}
	}
	return ret;
}

static UnifiedTerms gather_terms(const Index& i) {
	UnifiedTerms ret;
	for (const auto& p : i.vars) {
		for (uint d : p.second) {
			ret[d] = LightTree(p.first);
		}
	}
	for (const auto& p : i.rules) {
		for (auto& q : gather_terms(p.first, p.second)) {
			ret.emplace(q.first, q.second);
		}
	}
	return ret;
}

bool debug_index = false;
bool debug_ind = false;

UnifiedTerms unify(const Index* index, const LightTree& t, Index::Unified& unif) {
	UnifiedTerms ret;
	for (const auto& p : index->vars) {
		LightSymbol iv = p.first;
		for (uint d : p.second) {
			if (iv.rep) {
				ret[d] = unify_step(unif[d], {iv}, t);
			} else {
				if (t.kind() == LightTree::VAR) {
					if (t.var().rep) {
						ret[d] = unify_step(unif[d], {t.var()}, LightTree(iv));
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
					ret[q.first] = unify_step(unif[q.first], {tv}, q.second);
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
	}
	return ret;
}

uint Index::add(const LightTree& t) {
	uint ind = size++;
	exprs.push_back(t);
	add_to_index(this, t, ind);
	return ind;
}

Index::Unified Index::unify(const LightTree& t) const {
	Index::Unified unif;
	UnifiedTerms terms = prover::unify(this, t, unif);

	for (const auto& p : unif) {
		LightTree tr = exprs[p.first];
		LightTree x = terms[p.first];
		if (x.empty()) {
			unif[p.first].ok = false;
			continue;
		}
		if (!(apply(p.second, tr) == apply(p.second, t) && apply(p.second, t) == x)) {
			cout << "FAILURE" << endl << endl;
			debug_ind = true;
			prover::unify(this, t, unif);


			cout << "unification failure: " << p.first << endl;
			cout << "index:" << endl;
			cout << show() << endl;
			cout << "term:" << endl;
			cout << "\t" << prover::show(t) << endl;
			cout << "tr:" << endl;
			cout << "\t" << prover::show(tr) << endl;

			cout << "apply(p.second, tr): " << prover::show(apply(p.second, tr)) << endl;
			cout << "apply(p.second, t): " << prover::show(apply(p.second, t)) << endl;
			cout << "terms[p.first]: " << prover::show(terms[p.first]) << endl;
			cout << "sub: " << endl << prover::show(p.second) << endl;
			exit(0);
		}
	}
	return unif;
}

string Index::show() const {
	string ret;
	for (const auto&  p : showVector(this)) {
		ret += to_string(p.first) + " -> " + p.second + "\n";
	}
	return ret;
}

}}}


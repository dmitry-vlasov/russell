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

static void gather(const Rule* r, UnifiedTerms& u, UnifiedTerms w[], uint sz) {
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

static UnifiedTerms gather_terms(const Index* i);

static UnifiedTerms gather_terms(const Rule* r, const Index::Node& n) {
	UnifiedTerms ret;
	UnifiedTerms un[n.child.size()];
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

static UnifiedTerms gather_terms(const Index* i) {
	UnifiedTerms ret;
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

LightTree try_to_expand_subst(Subst& unif, LightSymbol v, LightTree t) {
	LightTree t_substituted = apply(unif, t);
	vector<const LightTree*> to_unify({&t_substituted});
	if (unif.maps(v.lit)) {
		to_unify.push_back(&unif.sub[v.lit]);
	}
	Unified u = unify(to_unify);
	if (!u.term.empty()) {
		LightTree term;
		if (v.type == u.term.type()) {
			term = u.term;
		} else if (Rule* super = find_super(u.term.type(), v.type)) {
			term = LightTree(super, new LightTree(u.term));
		}
		if (!term.empty() && unif.consistent(v.lit, term)) {
			unif.compose(Subst(v, term));
			return term;
		}
	}
	return LightTree();
}

UnifiedTerms unify(const Index* index, const LightTree& t, Index::Unified& unif) {
	UnifiedTerms ret;
	for (const auto& p : index->vars) {
		LightSymbol iv = p.first;
		for (uint d : p.second) {
			if (iv.rep) {
				ret[d] = try_to_expand_subst(unif[d], iv, t);
			} else {
				if (t.kind() == LightTree::VAR) {
					if (t.var().rep) {
						ret[d] = try_to_expand_subst(unif[d], t.var(), LightTree(iv));
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
			UnifiedTerms un[n.child.size()];
			int c = 0;
			for (const auto& i : n.child) {
				un[c++] = unify(i.get(), *(ch++)->get(), unif);
			}
			for (const auto& p : un[0]) {
				uint d = p.first;
				LightTree::Children ch;
				ch.push_back(make_unique<LightTree>(p.second));
				uint k = 1;
				for (; k < c; ++ k) {
					if (!un[k][d].empty()) {
						ch.push_back(make_unique<LightTree>(un[k][d]));
					} else {
						break;
					}
				}
				if (k == c) {
					ret[d] = LightTree(t.rule(), ch);
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
			continue;
		}
		if (!(apply(p.second, tr) == apply(p.second, t) && apply(p.second, t) == x)) {
			cout << "unification failure:" << endl;
		}
	}

	return unif;
}

string Index::show() const {
	string ret;
	for (const auto&  p : showVector(this)) {
		ret += p.second + "\n";
	}
	return ret;
}

}}}


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

void unify(const Index* index, const LightTree& t, Index::Unified& inif) {
	/*for (const auto& p : index->vars) {
		LightSymbol v = p.first;
		if (v.rep) {
			if (v.type == t.type()) {
				for (uint d : p.second) {
					unif[d].emplace_back(v, t);
				}
			} else if (Rule* super = find_super(t.type(), v.type)) {
				for (uint d : p.second) {
					unif[d].emplace_back(v, LightTree(super, new LightTree(t)));
				}
			}
		} else {
			if (t.kind() == LightTree::VAR && v == t.var()) {
				for (uint d : p.second) {
					unif[d];
				}
			}
		}
	}
	if (t.kind() == LightTree::VAR) {
		LightSymbol tv = t.var();
		if (tv.rep) {
			for (const auto& p : index->vars) {
				LightSymbol iv = p.first;
				if (iv.type == tv.type) {
					for (uint d : p.second) {
						unif[d].emplace_back(tv, LightTree(iv));
					}
				} else if (Rule* super = find_super(iv.type, tv.type)) {
					for (uint d : p.second) {
						unif[d].emplace_back(tv, LightTree(super, new LightTree(iv)));
					}
				}
			}
			for (const auto& p : index->rules) {
				const Rule* r = p.first;
				const Index::Node& n = p.second;
				if (tv.type == r->type()) {
					for (const auto& q : gather_terms(r, n)) {
						unif[q.first].emplace_back(tv, *q.second);
					}
				} else if (Rule* super = find_super(r->type(), tv.type)) {
					for (const auto& q : gather_terms(r, n)) {
						unif[q.first].emplace_back(tv, LightTree(super, new LightTree(*q.second)));
					}
				}
			}
		} else {
			for (const auto& p : index->vars) {
				LightSymbol iv = p.first;
				if (iv == tv) {
					for (uint d : p.second) {
						unif[d];
					}
				}
			}
		}
	} else if (index->rules.count(t.rule())) {
		const Index::Node& n = index->rules.at(t.rule());
		for (uint d : n.leafs) {
			unif[d];
		}
		auto ch = t.children().begin();
		VarTreeMap un[n.child.size()];
		int c = 0;
		for (const auto& i : n.child) {
			unify(i.get(), *(ch++)->get(), unif);
		}
	}*/
}

uint Index::add(const LightTree& t) {
	uint ind = size++;
	exprs.push_back(t);
	add_to_index(this, t, ind);
	return ind;
}

bool check_unification(const Unified& unif, const vector<const LightTree*>& ex);

Index::Unified Index::unify(const LightTree& t) const {
	Index::Unified unif;
	prover::unify(this, t, unif);

	for (const auto& p : unif) {
		LightTree tr = exprs[p.first];
		if (!check_unification(p.second, {&t, &tr})) {
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


#include "rus_prover_index.hpp"
#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

typedef map<uint, unique_ptr<LightTree>> MatchedTerms;

static void gather(const Rule* r, MatchedTerms& u, MatchedTerms w[], uint sz) {
	for (auto& p : w[0]) {
		uint d = p.first;
		LightTree::Children ch;
		ch.emplace_back(p.second.release());
		int i = 1;
		for (; i < sz; ++ i) {
			assert(w[i].count(d));
			ch.emplace_back(w[i][d].release());
		}
		u[d] = make_unique<LightTree>(r, ch);
	}
}

static MatchedTerms gather_terms(const Index* i);

static MatchedTerms gather_terms(const Rule* r, const Index::Node& n) {
	MatchedTerms ret;
	MatchedTerms un[n.child.size()];
	for (uint d : n.leafs) {
		ret[d] = make_unique<LightTree>(r, LightTree::Children());
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
static MatchedTerms gather_terms(const Index* i) {
	MatchedTerms ret;
	for (const auto& p : i->vars) {
		for (uint d : p.second) {
			ret[d] = make_unique<LightTree>(p.first);
		}
	}
	for (const auto& p : i->rules) {
		for (auto& q : gather_terms(p.first, p.second)) {
			ret.emplace(q.first, q.second.release());
		}
	}
	return ret;
}

static void intersect(Index::Unified& u, Index::Unified w[], uint sz) {
	for (auto p : w[0]) {
		uint d = p.first;
		Subst s = p.second;
		int i = 1;
		for (; i < sz; ++ i) {
			if (!w[i].count(d) || !s.join(w[i][d])) {
				break;
			}
		}
		if (i == sz) {
			u[d].join(s);
		}
	}
}

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

void Index::add(const LightTree& t, uint s) {
	if (t.kind() == LightTree::VAR) {
		vars[t.var()].insert(s);
	} else {
		if (!t.children().size()) {
			rules[t.rule()].leafs.insert(s);
		} else {
			bool is_new = !rules.count(t.rule());
			vector<unique_ptr<Index>>& ch = rules[t.rule()].child;
			if (is_new) {
				for (const auto& c : t.children()) {
					ch.push_back(make_unique<Index>());
				}
			}
			auto i = ch.begin();
			for (const auto& c : t.children()) {
				(*(i++))->add(*c.get(), s);
			}
		}
	}
}
Index::Unified Index::match_forth(const LightTree& t) const {
	Unified unif;
	for (const auto& p : vars) {
		LightSymbol v = p.first;
		if (v.rep) {
			if (v.type == t.type()) {
				for (uint d : p.second) {
					unif[d].join(v.lit, t);
				}
			} else if (Rule* super = find_super(t.type(), v.type)) {
				for (uint d : p.second) {
					unif[d].join(v.lit, LightTree(super, new LightTree(t)));
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
	if (t.kind() == LightTree::NODE && rules.count(t.rule())) {
		const Node& n = rules.at(t.rule());
		for (uint d : n.leafs) {
			unif[d];
		}
		auto ch = t.children().begin();
		Unified un[n.child.size()];
		int c = 0;
		for (const auto& i : n.child) {
			Unified match = i->match_forth(*(ch++)->get());
			un[c++] = match;
		}
		if (c > 0) {
			intersect(unif, un, c);
		}
	}
	return unif;
}

Index::Unified Index::match_back(const LightTree& t) const {
	Unified unif;
	if (t.kind() == LightTree::VAR) {
		LightSymbol tv = t.var();
		if (tv.rep) {
			for (const auto& p : vars) {
				LightSymbol iv = p.first;
				if (iv.type == tv.type) {
					for (uint d : p.second) {
						unif[d].join(tv.lit, iv);
					}
				} else if (Rule* super = find_super(iv.type, tv.type)) {
					for (uint d : p.second) {
						unif[d].join(tv.lit, LightTree(super, new LightTree(iv)));
					}
				}
			}
			for (const auto& p : rules) {
				const Rule* r = p.first;
				const Node& n = p.second;
				if (tv.type == r->type()) {
					for (const auto& q : gather_terms(r, n)) {
						unif[q.first].join(tv.lit, *q.second);
					}
				} else if (Rule* super = find_super(r->type(), tv.type)) {
					for (const auto& q : gather_terms(r, n)) {
						unif[q.first].join(tv.lit, LightTree(super, new LightTree(*q.second)));
					}
				}
			}
		} else {
			for (const auto& p : vars) {
				LightSymbol iv = p.first;
				if (iv == tv) {
					for (uint d : p.second) {
						unif[d];
					}
				}
			}
		}
	} else if (rules.count(t.rule())) {
		const Node& n = rules.at(t.rule());
		for (uint d : n.leafs) {
			unif[d];
		}
		auto ch = t.children().begin();
		Unified un[n.child.size()];
		int c = 0;
		for (const auto& i : n.child) {
			un[c++] = i->match_back(*(ch++)->get());
		}
		if (c > 0) {
			intersect(unif, un, c);
		}
	}
	return unif;
}


void collect_vars(const LightTree& tree, set<uint> vars) {
	if (tree.kind() == LightTree::VAR) {
		vars.insert(tree.var().lit);
	} else {
		for (const auto& c : tree.children()) {
			collect_vars(*c.get(), vars);
		}
	}
}

struct VarTree {
	VarTree(LightSymbol v, const LightTree& t) : var(v), tree(t) { }
	VarTree(LightSymbol v, LightTree&& t) : var(v), tree(std::move(t)) { }
	LightSymbol var;
	LightTree   tree;
};

bool consistent_for_unify(const Subst& s, const VarTree& vt) {
	set<uint> x_vars;
	collect_vars(vt.tree, x_vars);
	for (uint y : x_vars) {
		auto i = s.sub.find(y);
		if (i != s.sub.end()) {
			set<uint> y_vars;
			collect_vars(i->second, y_vars);
			if (y_vars.find(vt.var.lit) != y_vars.end()) {
				return false;
			}
		}
	}
	return true;
}

bool add_var_tree(Subst& s, const VarTree& vt) {
	if (!consistent_for_unify(s, vt)) {
		return false;
	}
	auto i = s.sub.find(vt.var.lit);
	if (i == s.sub.end()) {
		s = compose(s, Subst(vt.var.lit, vt.tree));
	} else {
		if (i->second.kind() == LightTree::VAR) {
			LightSymbol v = i->second.var();
			s.sub.erase(vt.var.lit);
			s = compose(s, Subst(vt.var.lit, vt.tree));
			s = compose(s, Subst(v.lit, vt.tree));
		} else {
			Unified unif = unify({&vt.tree, &i->second});
			if (unif.sub.ok) {
				s = compose(s, unif.sub);
			} else {
				return false;
			}
		}
	}
	return true;
}


typedef map<uint, vector<VarTree>> VarTreeMap;

static void intersect(VarTreeMap& u, VarTreeMap w[], uint sz) {
	for (auto p : w[0]) {
		uint d = p.first;
		vector<VarTree> s = p.second;
		int i = 1;
		for (; i < sz; ++ i) {
			if (!w[i].count(d)) {
				break;
			} else {
				for (auto vt : w[i][d]) {
					s.push_back(vt);
				}
			}
		}
		if (i == sz) {
			u[d] = s;
		} else {
			u.erase(d);
		}
	}
}

VarTreeMap unify(const Index* index, const LightTree& t) {
	VarTreeMap unif;
	for (const auto& p : index->vars) {
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
			un[c++] = unify(i.get(), *(ch++)->get());
		}
		if (c > 0) {
			intersect(unif, un, c);
		}
	}
	return unif;
}

Subst unify(const vector<VarTree>& vect) {
	Subst s;
	for (const auto& vt : vect) {
		if (!add_var_tree(s, vt)) {
			break;
		}
	}
	return s;
}

Index::Unified Index::unify(const LightTree& t) const {
	VarTreeMap m = prover::unify(this, t);
	Unified ret;
	for (const auto& p : m) {
		uint d = p.first;
		Subst s = prover::unify(p.second);
		if (s.ok) {
			ret[d] = s;
		}
	}
	return ret;
}


string Index::show() const {
	string ret;
	for (const auto&  p : showVector(this)) {
		ret += p.second + "\n";
	}
	return ret;
}













































/*VarTreeMap unify(const Index* index, const LightTree& t) {
	VarTreeMap unif;
	for (const auto& p : index->vars) {
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
			un[c++] = unify(i.get(), *(ch++)->get());
		}
		if (c > 0) {
			intersect(unif, un, c);
		}
	}
	return unif;
}*/

}}}


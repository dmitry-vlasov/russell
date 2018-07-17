#pragma once

#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

template<class D>
using Unified = map<D, Substitution>;

template<class D>
using UnifiedTerms = map<D, Tree*>;

template<class D>
struct Index {
	typedef D Data;
	struct Node {
		vector<Data>   data;
		vector<Index*> child;
	};
	map<const Rule*, Node>     rules;
	map<Symbol, vector<Data>> vars;

	void add(const Tree* t, const D& d) {

		cout << "\nADDING: " << rus::show(t) << " TO\n" << show() << "\n";

		if (t->kind() == Tree::VAR) {
			vars[*t->var()].push_back(d);
		} else {
			if (!t->children().size()) {
				rules[t->rule()].data.push_back(d);
			} else {
				bool is_new = !rules.count(t->rule());
				vector<Index<D>*>& ch = rules[t->rule()].child;

				if (is_new) {
					for (const auto& c : t->children()) {
						ch.push_back(new Index<D>);
					}
				}
				auto i = ch.begin();
				for (const auto& c : t->children()) {
					(*(i++))->add(c.get(), d);
				}
			}
		}
		cout << "\nADDING DONE: " << rus::show(t) << " TO\n" << show() << "\n";
	}
	Unified<Data> unify_forth(const Tree* t) const {
		Unified<Data> unif;
		for (const auto& p : vars) {
			const Symbol& v = p.first;
			if (v.type() == t->type()) {
				for (const Data& d : p.second)
					unif[d].join(v.lit, *t);
			} else if (Rule* super = find_super(t->type(), v.type())) {
				for (const Data& d : p.second)
					unif[d].join(v.lit, Tree(super->id(), {new Tree(*t)}));
			}
		}
		if (t->kind() == Tree::NODE && rules.count(t->rule())) {
			const Node& n = rules.at(t->rule());
			for (const Data& d : n.data) unif[d];
			auto ch = t->children().begin();
			Unified<Data> un[n.child.size()];
			int c = 0;
			for (const Index* i : n.child) {
				un[c++] = i->unify_forth((ch++)->get());
			}
			if (c > 0) intersect(unif, un, c);
		}
		return unif;
	}
	Unified<Data> unify_back(const Tree* t) const {

		cout << "\nUNIFYING: " << rus::show(t) << " WITH\n" << show() << "\n";

		Unified<Data> unif;
		if (t->kind() == Tree::VAR) {
			Symbol tv = *t->var();
			for (const auto& p : vars) {
				Symbol iv = p.first;
				if (iv.type() == tv.type()) {
					for (const Data& d : p.second)
						unif[d].join(tv.lit, iv);
				} else if (Rule* super = find_super(iv.type(), tv.type())) {
					for (const Data& d : p.second) {
						Tree tr(super->id(), {new Tree(iv)});
						unif[d].join(tv.lit, tr);
					}
				}
			}
			for (const auto& p : rules) {
				const Rule* r = p.first;
				const Node& n = p.second;
				if (tv.type() == r->type()) {
					for (const auto& q : gather_terms(r, n))
						unif[q.first].join(tv.lit, *q.second);
				} else if (Rule* super = find_super(r->type(), tv.type())) {
					for (const auto& q : gather_terms(r, n)) {
						Tree tr(super->id(), {new Tree(*q.second)});
						unif[q.first].join(tv.lit, tr);
					}
				}
			}
		} else if (rules.count(t->rule())) {
			const Node& n = rules.at(t->rule());
			for (const Data& d : n.data) unif[d];
			auto ch = t->children().begin();
			Unified<Data> un[n.child.size()];
			int c = 0;
			for (const Index* i : n.child) {
				un[c++] = i->unify_back((ch++)->get());
			}
			if (c > 0) intersect(unif, un, c);
		}
		return unif;
	}
	~Index() {
		for (auto& p : rules)
			for (auto& i : p.second.child)
				delete i;
	}

	string show() const {
		string ret;
		for (const auto&  p : showVector()) {
			ret += p.second + "\n";
		}
		return ret;
	}

private:
	map<D, string> showVector() const {
		map<D, string> ret;
		for (const auto& p : vars) {
			for (const auto& d : p.second) {
				ret[d] = rus::show(p.first);
			}
		}
		for (const auto& p : rules) {
			const Rule* r = p.first;
			for (const auto& d : p.second.data) {
				const vector<Index*>& ch = p.second.child;
				map<D, string> show_ch[ch.size()];
				int c = 0;
				for (auto ind : ch) {
					 show_ch[c++] = ind->showVector();
				}
				map<D, vector<string>> intersected;
				if (c > 0) {
					intersect_show(intersected, show_ch, c);
				}
				for (auto pr : intersected) {
					string str;
					int x = 0;
					for (auto s : r->term.symbols) {
						if (s.cst) {
							str += rus::show(s);
						} else {
							str += pr.second[x++];
						}
					}
					ret[pr.first] = str;
				}
			}
		}
		return ret;
	}

	static UnifiedTerms<Data> gather_terms(const Rule* r, const Node& n) {
		UnifiedTerms<Data> ret;
		UnifiedTerms<Data> un[n.child.size()];
		for (const Data& d : n.data) ret[d] = new Tree(r->id(), Tree::Children());
		int c = 0;
		for (const auto i : n.child) {
			un[c++] = gather_terms(i);
		}
		if (c > 0) gather(r, ret, un, c);
		return ret;
	}
	static UnifiedTerms<Data> gather_terms(const Index* i) {
		UnifiedTerms<Data> ret;
		for (const auto& p : i->vars)
			for (const auto& d : p.second)
			ret[d] = new Tree(p.first);
		for (const auto& p : i->rules) {
			for (const auto& q : gather_terms(p.first, p.second))
				ret[q.first] = q.second;
		}
		return ret;
	}
	static void gather(const Rule* r, UnifiedTerms<D>& u, UnifiedTerms<D> w[], uint sz) {
		for (auto p : w[0]) {
			D d = p.first;
			Tree::Children ch;
			ch.emplace_back(p.second);
			int i = 1;
			for (; i < sz; ++ i) {
				assert(w[i].count(d));
				ch.emplace_back(w[i][d]);
			}
			u[d] = new Tree(r->id(), ch);
		}
	}
	static void intersect(Unified<D>& u, Unified<D> w[], uint sz) {
		for (auto p : w[0]) {
			D d = p.first;
			Substitution s = p.second;
			int i = 1;
			for (; i < sz; ++ i) {
				if (!w[i].count(d) || !s.join(w[i][d])) {
					break;
				}
			}
			if (i == sz) u[d] = s;
		}
	}
	static void intersect_show(map<D, vector<string>>& u, map<D, string> w[], uint sz) {
		for (auto p : w[0]) {
			D d = p.first;
			vector<string> vstr;
			int i = 1;
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
};

}}}


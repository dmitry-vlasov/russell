#pragma once

#include "rus_prover.hpp"

namespace mdl { namespace rus {

Rule* find_super(const Type* type, const Type* super);

namespace prover {

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
	map<User<Rule>, Node>     rules;
	map<Symbol, vector<Data>> vars;

	void add(const Tree* t, const D& d) {
		if (t->kind == Tree::VAR) {
			vars[*t->var()].push_back(d);
		} else {
			if (!t->children().size())
				rules[t->rule()].data.push_back(d);
			else {
				bool is_new = !rules.count(t->rule());
				vector<Index<D>*>& ch = rules[t->rule()].child;
				if (is_new)
					for (const auto& c : t->children())
						ch.push_back(new Index<D>);
				auto i = ch.begin();
				for (const auto& c : t->children()) {
					(*(i++))->add(c.get(), d);
				}
			}
		}
	}
	Unified<Data> unify_forth(const Tree* t) const {
		Unified<Data> unif;
		for (const auto& p : vars) {
			Symbol v = p.first;
			if (v.type() == t->type()) {
				for (const Data& d : p.second)
					unif[d].join(v, t);
			} else if (Rule* super = find_super(t->type(), v.type())) {
				for (const Data& d : p.second) {
					Tree tr(super, {new Tree(*t)});
					unif[d].join(v, &tr);
				}
			}
		}
		if (rules.count(t->rule())) {
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
		Unified<Data> unif;
		if (t->kind == Tree::VAR) {
			Symbol tv = *t->var();
			for (const auto& p : vars) {
				Symbol iv = p.first;
				if (iv.type() == tv.type()) {
					for (const Data& d : p.second)
						unif[d].join(tv, iv);
				} else if (Rule* super = find_super(iv.type(), tv.type())) {
					for (const Data& d : p.second) {
						Tree tr(super, {new Tree(iv)});
						unif[d].join(tv, &tr);
					}
				}
			}
			for (const auto& p : rules) {
				const Rule* r = p.first.get();
				const Node& n = p.second;
				if (tv.type() == r->type()) {
					for (const auto& q : gather_terms(r, n))
						unif[q.fisrt].join(tv, q.second);
				} else if (Rule* super = find_super(r->type(), tv.type())) {
					for (const auto& q : gather_terms(r, n)) {
						Tree tr(super, {new Tree(q.second)});
						unif[q.first].join(tv, &tr);
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
private:
	UnifiedTerms<Data> gather_terms(Rule* r, const Node& n) {
		UnifiedTerms<Data> ret;
		UnifiedTerms<Data> un[n.child.size()];
		for (const Data& d : n.data) ret[d] = new Tree(r);
		int c = 0;
		for (const auto i : n.child) {
			un[c++] = gather_terms(i);
		}
		if (c > 0) gather(r, ret, un, c);
		return ret;
	}
	UnifiedTerms<Data> gather_terms(const Index* i) {
		UnifiedTerms<Data> ret;
		for (const auto& p : i->vars)
			for (const auto& d : p.second)
			ret[d] = new Tree(p.first);
		for (const auto& p : i->rules) {
			for (auto q : gather_terms(p.first, p.second))
				ret[q.first] = q.second;
		}
		return ret;
	}
	static void gather(Rule* r, UnifiedTerms<D>& u, UnifiedTerms<D> w[], uint sz) {
		for (auto p : w[0]) {
			D d = p.first;
			Tree::Children ch;
			ch.push_back(p.second);
			int i = 1;
			for (; i < sz; ++ i) {
				assert(w[i].count(d));
				ch.push_back(w[i][d]);
			}
			u[d] = new Tree(r, ch);
		}
	}
	static void intersect(Unified<D>& u, Unified<D> w[], uint sz) {
		for (auto p : w[0]) {
			D d = p.first;
			Substitution s = p.second;
			int i = 1;
			for (; i < sz; ++ i)
				if (!w[i].count(d) || !s.join(w[i][d]))
					break;
			if (i == sz) u[d] = s;
		}
	}
};

Index<PropRef>& assertion_index();

}}}


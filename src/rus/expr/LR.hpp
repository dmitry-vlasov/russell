#pragma once

#include "common.hpp"
#include "rus/expr/table.hpp"

namespace mdl { namespace rus { namespace expr {

struct Item {
	Item(Product* p, Symbol l) : prod(p), dot(0), lookahead(l) { }
	Product* prod;
	uint     dot;
	Symbol   lookahead;
	Symbol after_dot() const { return prod->right[dot]; }
	Symbol before_dot() const { return prod->right[dot - 1]; }
	bool completed() const { return dot == prod->right.size(); }
};

string show(const Item&);

template<typename> struct Less;

template<>
struct Less<Item> {
	bool operator () (const Item& item1, const Item& item2) const {
			 if (item1.prod < item2.prod) return true;
		else if (item1.prod > item2.prod) return false;
		else if (item1.dot < item2.dot)   return true;
		else if (item1.dot > item2.dot)   return false;
		else if (item1.lookahead < item2.lookahead) return true;
		else return false;
	}
};

struct State {
	enum Kind { FINAL, TRIAL };
	State(Kind k) :
		items(), ind(k == FINAL ? count++ : -1) { }
	State(const State& st, Kind k) :
		items(st.items), ind(k == FINAL ? count++ : st.ind) { }
	set<Item, Less<Item>> items;
	uint                  ind;
	static uint           count;
};

string show(const State& st);

template<>
struct Less<State*> {
	bool operator () (const State* s1, const State* s2) const {
		static Less<Item> less;
			 if (s1->items.size() < s2->items.size()) return true;
		else if (s1->items.size() > s2->items.size()) return false;
		else {
			for (auto i = s1->items.begin(), j = s2->items.begin(); i != s1->items.end(); ++ i, ++ j) {
				if (less(*i, *j)) return true;
				else if (less(*j, *i)) return false;
			}
		}
		return false;
	}
};

struct LR {
	~ LR();

	Set<Symbol>                symbol_set;
	Set<Symbol>                terminals;
	Set<Symbol>                non_terminals;

	Map<Symbol, Set<Product*>> rule_map;
	Map<Symbol, Set<Symbol>>   first_map;
	Map<Symbol, Set<Symbol>>   follow_map;
	Set<State*, Less<State*>>  state_set;
	Map<Type*, State*>         init_map;
	Set<Product*>              init_prods;

	vector<State*>             state_vect;
	vector<Product*>           prod_vect;

	Table table;
};

string show(const LR&);

}}} // namespace mdl::rus::expr

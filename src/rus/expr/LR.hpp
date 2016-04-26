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
	Set<Item, Less<Item>> items;
	uint                  ind;
};

string show(const State& st);

template<>
struct Less<State*> {
	bool operator () (const State* s1, const State* s2) const {
		static Less<Item> less;
			 if (s1->items.s.size() < s2->items.s.size()) return true;
		else if (s1->items.s.size() > s2->items.s.size()) return false;
		else {
			for (auto i = s1->items.s.begin(), j = s2->items.s.begin(); i != s1->items.s.end(); ++ i, ++ j) {
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
	Map<Type*, Product*>       init_map;

	vector<State*>             state_vect;
	vector<Product*>           prod_vect;

	Table table;
};

string show(const LR&);

}}} // namespace mdl::rus::expr

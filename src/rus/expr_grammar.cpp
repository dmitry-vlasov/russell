#include "rus/expr_grammar.hpp"

namespace mdl { namespace rus { namespace expr {

static Symbol make_non_term(Type* t, const char* prefix = "") {
	string s = prefix;
	s += Rus::get().lex.ids.toStr(t->id);
	return Symbol(s, t);
}

static uint prod_count = 0;

Product::Product(rus::Rule* r) :
left(make_non_term(r->type)), right(), rule(r), ind(prod_count++) {
	for (auto s : r->term) {
		if (s.symb.type)
			right.push_back(make_non_term(s.symb.type));
		else
			right.push_back(s.symb);
	}
}

Product::Product(Symbol l, Symbol r) : left(l), right(), rule(nullptr), ind(prod_count++) {
	right.push_back(r);
}

string show(const Product& p) {
	string str;
	str += show(p.left) + " → ";
	for (auto s : p.right)
		str += show(s) + " ";
	return str;
}

struct Item {
	Item(Product* p, Symbol l) : prod(p), dot(0), lookahead(l) { }
	Product* prod;
	uint     dot;
	Symbol   lookahead;
	Symbol after_dot() const { return prod->right[dot]; }
	Symbol before_dot() const { return prod->right[dot - 1]; }
	bool completed() const { return dot == prod->right.size(); }
};

string show(const Item& it) {
	string str = "[";
	str += show(it.prod->left) + " → ";
	for (uint i = 0; i < it.prod->right.size(); ++ i) {
		if (i == it.dot) str += " .";
		str += show(it.prod->right[i]) + " ";
	}
	str += ", " + show(it.lookahead) + "]";
	return str;
}

template<typename> struct Less;

template<>
struct Less<Item> {
	bool operator () (const Item& item1, const Item& item2) const {
			 if (item1.prod < item2.prod) return true;
		else if (item1.prod > item2.prod) return false;
		else if (item1.dot < item2.dot)   return true;
		else if (item1.dot > item2.dot)   return true;
		else if (item1.lookahead < item2.lookahead) return true;
		else return false;
	}
};


struct State {
	set<Item, Less<Item>> items;
	uint                  ind;
	static uint           count;
};

uint State::count = 0;

string show(const Action& act) {
	switch (act.kind) {
	case Action::ERROR:
		return string("<err>");
	case Action::ACCEPT:
		return string("<acc>");
	case Action::REDUCE:
		return string("r_") + to_string(act.val.prod->ind);
	case Action::SHIFT:
		return string("s_") + to_string(act.val.state->ind);
	default: assert(false && "impossible"); return "";
	}
}

template<>
struct Less<State*> {
	bool operator () (const State* s1, const State* s2) {
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

	set<Symbol>                symbol_set;
	map<Symbol, set<Product*>> rule_map;
	map<Symbol, set<Symbol>>   first_map;
	map<Symbol, set<Symbol>>   follow_map;
	set<State*, Less<State*>>  state_set;
	map<Type*, State*>         init_map;
	set<Product*>              init_prods;

	vector<State*>             state_vect;
	vector<Product*>           prod_vect;

	Table table;
};

LR::~ LR() {
	for (State* s : state_vect) delete s;
	for (Product* p : prod_vect) delete p;
}

static LR lr;

Table& table() { return lr.table; }



/*
SetOfltems CLOSURE(I) {
	repeat
		for ( each item [A -> a .B c, a] in I )
			for ( each production B -> d in G )
				for ( each terminal x in FOLLOW (B) )
					add [B -> .d, x] to set I;
		until no more items are added to I;
	return I;
}
*/

void make_closure(State& state) {
	bool new_items = false;
	do {
		new_items = false;
		for (const Item& i : state.items) {
			Symbol b = i.after_dot();
			for (Product* p : lr.rule_map[b]) {
				for (Symbol x : lr.follow_map[b]) {
					Item j(p, x);
					if (state.items.find(j) == state.items.end()) {
						new_items = true;
						state.items.insert(j);
					}
				}
			}
		}
	} while (!new_items);
}

void complement_tables(State* from, Symbol x, State* to) {
	lr.table.gotos[from][x] = to;
	Action act;
	for (const Item& i : from->items) {
		if (i.completed()) {
			if (act.kind != Action::ERROR)
				throw Error("non LR(1) grammar");
			else {
				if (lr.init_prods.find(i.prod) != lr.init_prods.end())
					act.kind = Action::ACCEPT;
				else
					act.kind = Action::REDUCE;
				act.val.prod = i.prod;
			}
		} else {
			if (act.kind != Action::ERROR)
				throw Error("non LR(1) grammar");
			else if (is_terminal(x) && i.before_dot() == x) {
				act.kind = Action::SHIFT;
				act.val.state = to;
			}
		}
	}
	lr.table.actions[from][x] = act;
}

/*
SetOfltems GOTO(I, X) {
	initialize J to be the empty set;
	for ( each item [A -> a .X b, c] in I )
		add item [A -> a X. b, c] to set J;
	return CLOSURE(J);
}
 */

State make_goto(const State& from, Symbol X) {
	State to;
	for (Item it : from.items) {
		if (it.dot < it.prod->right.size()) {
			it.dot += 1;
			to.items.insert(it);
		}
	}
	make_closure(to);
	return to;
}



void collect_states() {
	lr.table.actions.clear();
	lr.table.gotos.clear();
	bool new_state = false;
	do {
		new_state = false;
		for (State* from : lr.state_set) {
			for (Symbol x : lr.symbol_set) {
				State t = make_goto(*from, x);
				if (!t.items.empty() && (lr.state_set.find(&t) == lr.state_set.end())) {
					State* to = new State(t);
					to->ind = State::count++;
					lr.state_vect.push_back(to);
					lr.state_set.insert(to);
					new_state = true;
					complement_tables(from, x, to);
				}
			}
		}
	} while (new_state);
}


void add_rule(rus::Rule* r) {
	Product* prod = new Product(r);
	lr.prod_vect.push_back(prod);
	lr.rule_map[prod->left].insert(prod);

	// Arrange first:
	Symbol s = prod->right[0];
	if (is_terminal(s))
		lr.first_map[prod->left].insert(s);
	else
		lr.first_map[prod->left].insert(lr.first_map[s].begin(), lr.first_map[s].end());

	// Arrange follow:
	for (uint i = 0; i < prod->right.size(); ++ i) {
		s = prod->right[i];
		if (i + 1 < prod->right.size()) {
			Symbol x = prod->right[i + 1];
			if (is_non_term(s)){
				lr.follow_map[s].insert(lr.first_map[x].begin(), lr.first_map[x].end());
			}
		} else if (is_non_term(s)) {
			lr.follow_map[s].insert(lr.follow_map[prod->left].begin(), lr.follow_map[prod->left].end());
		}
	}

	// Add initial state
	if (lr.symbol_set.find(prod->left) == lr.symbol_set.end()) {
		Symbol s = make_non_term(r->type);
		Symbol s_prime = make_non_term(r->type, "prime_");
		Product* p = new Product(s_prime, s);
		lr.prod_vect.push_back(p);
		Item it(p, end_marker());
		State* init = new State;
		init->items.insert(it);
		make_closure(*init);
		lr.state_set.insert(init);
		lr.state_vect.push_back(init);
		lr.init_prods.insert(p);
		lr.init_map[r->type] = init;
	}

	// Add symbols
	lr.symbol_set.insert(prod->left);
	for (auto s : prod->right)
		lr.symbol_set.insert(s);

	collect_states();
}


}}} // namespace mdl::rus::expr

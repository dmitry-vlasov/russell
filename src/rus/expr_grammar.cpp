#include "common.hpp"
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
	string str = "item [";
	str += show(it.prod->left) + " → ";
	for (uint i = 0; i < it.prod->right.size(); ++ i) {
		if (i == it.dot) str += " .";
		str += show(it.prod->right[i]) + " ";
	}
	if (it.dot == it.prod->right.size())
		str += ".";
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

uint State::count = 0;

string show(const State& st) {
	string str = "state ";
	str += to_string(st.ind) + " {\n";
	for (const Item& it : st.items) {
		str += "\t" + show(it) + "\n";
	}
	str += "}\n";
	return str;
}

string show(const Action& act) {
	switch (act.kind) {
	case Action::ERROR:
		return string("<err>");
	case Action::ACCEPT:
		return string("<acc> ") + to_string(act.val.prod->ind);
	case Action::REDUCE:
		return string("<red> ") + to_string(act.val.prod->ind);
	case Action::SHIFT:
		return string("<shft> ") + to_string(act.val.state->ind);
	default:
		return string("<IMPOSSIBLE> ") + to_string(act.kind);
		//assert(false && "impossible"); return "";
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

	bool has_rule(Symbol s) {
		return rule_map.find(s) != rule_map.end();
	}
	bool has_first(Symbol s) {
		return first_map.find(s) != first_map.end();
	}
	bool has_follow(Symbol s) {
		return follow_map.find(s) != follow_map.end();
	}
	bool has_init(Type* t) {
		return init_map.find(t) != init_map.end();
	}

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

string show(const LR& lr) {
	string str = "LR = \n";

	str += "Symbols:\n\t";
	for (auto s : lr.symbol_set)
		str += show(s) + " ";
	str += "\n";

	str += "Rule map:\n";
	for (auto s : lr.rule_map) {
		str += "\t" + show(s.first) + " |--> \n";
		for (auto p : s.second)
			str += "\t\t" + show(*p) + "\n";
		str += "\n";
	}
	str += "\n";

	str += "First map:\n";
	for (auto p : lr.first_map) {
		str += "\t" + show(p.first) + " |--> {";
		for (auto s : p.second)
			str += show(s) + " ";
		str += "}\n";
	}
	str += "\n";

	str += "Follow map:\n";
	for (auto p : lr.follow_map) {
		str += "\t" + show(p.first) + " |--> {";
		for (auto s : p.second)
			str += show(s) + " ";
		str += "}\n";
	}
	str += "\n";

	str += "Products:\n";
	for (auto p : lr.prod_vect)
		str += "\t" + show(*p) + "\n";
	str += "\n";

	str += "Init prods:\n";
	for (auto p : lr.init_prods)
		str += "\t" + show(*p) + "\n";
	str += "\n";

	str += "Init map:\n";
	for (auto p : lr.init_map)
		str += "\t" + show_id(p.first->id) + " |--> " + show(*p.second) + "\n";
	str += "\n";

	str += "States:\n";
	for (State* s : lr.state_set)
		str += indent::paragraph(show(*s)) + "\n";
	str += "\n";

	return str;
}

Table& table() { return lr.table; }


/*
 *
typedef map<State*, map<Symbol, State*>> Gotos;
typedef map<State*, map<Symbol, Action>> Actions;
typedef map<Type*, State*>               Inits;

struct Table {
	Inits   inits;
	Gotos   gotos;
	Actions actions;
};
 */

string show(const Table& tab) {
	string str = "Tables:\n";
	str += "------------\n";
	str += "Gotos:\n";
	for (auto p1 : tab.gotos) {
		str += "\t" + to_string(p1.first->ind) + " x\n";
		for (auto p2 : p1.second) {
			str += "\t\t" + to_string(p2.second->ind) + " |--> " + to_string(p2.second->ind) + "\n";
		}
		str += "\n";
	}
	str += "\n";

	str += "Actions:\n";
	for (auto p1 : tab.actions) {
		str += "\t" + to_string(p1.first->ind) + " x\n";
		for (auto p2 : p1.second) {
			str += "\t\t" + show(p2.second) + " |--> " + show(p2.second) + "\n";
		}
		str += "\n";
	}
	str += "\n";

	str += "Inits:\n";
	for (auto p : tab.inits) {
		str += "\t" + show_id(p.first->id) +  " |--> " + to_string(p.second->ind) + "\n";
	}
	str += "\n";

	return str;
}

string show_lr() {
	string str;
	str += show(lr);
	str += show(table());
	return str;
}

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
			if (!lr.has_rule(b))
				continue;
			for (Product* p : lr.rule_map[b]) {
				if (!lr.has_follow(b))
					continue;
				for (Symbol x : lr.follow_map[b]) {
					Item j(p, x);
					if (state.items.find(j) == state.items.end()) {
						new_items = true;
						state.items.insert(j);
					}
				}
			}
		}
	} while (new_items);
}

void complement_tables(State* from, Symbol x, State* to) {
	lr.table.gotos[from][x] = to;
	Action act;
	for (const Item& i : from->items) {
		if (i.completed()) {
			if (act.kind != Action::ERROR) {
				cout << "already has action: " << show(act) << endl;
				if (lr.init_prods.find(i.prod) != lr.init_prods.end())
					act.kind = Action::ACCEPT;
				else
					act.kind = Action::REDUCE;
				act.val.prod = i.prod;
				cout << "going to be: " << show(act) << endl;
				cout << show_lr() << endl;
				throw Error("non LR(1) grammar");
			} else {
				if (lr.init_prods.find(i.prod) != lr.init_prods.end())
					act.kind = Action::ACCEPT;
				else
					act.kind = Action::REDUCE;
				act.val.prod = i.prod;
			}
		} else {
			if (act.kind != Action::ERROR) {
				cout << "already has action: " << show(act) << endl;
				act.kind = Action::SHIFT;
				act.val.state = to;
				cout << "going to be: " << show(act) << endl;
				cout << show_lr() << endl;
				throw Error("non LR(1) grammar");
			}
			else if (is_terminal(x) && i.after_dot() == x) {
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
	State to(State::TRIAL);
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


					cout << show(*to) << endl;
				}
			}
		}
	} while (new_state);
}


void add_rule(rus::Rule* r) {
	Product* prod = new Product(r);
	lr.prod_vect.push_back(prod);
	lr.rule_map[prod->left].insert(prod);

	cout << endl << show(*prod) << endl << endl;

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

		cout << endl << show(*p) << endl << endl;

		lr.prod_vect.push_back(p);
		Item it(p, end_marker());
		State* init = new State(State::FINAL);
		init->items.insert(it);
		make_closure(*init);

		cout << endl << show(*init) << endl << endl;

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


	cout << show_lr() << endl;
}


}}} // namespace mdl::rus::expr

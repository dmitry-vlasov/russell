#include "common.hpp"
#include "GLR.hpp"

namespace mdl { namespace rus { namespace expr {

LR lr;

namespace {

Symbol make_non_term(Type* t, const char* prefix = "") {
	string s = prefix;
	s += Rus::get().lex.ids.toStr(t->id);
	return Symbol(s, t);
}

Symbol make_terminal(Type* t, const char* postfix = "") {
	string s = Rus::get().lex.ids.toStr(t->id) + postfix;
	return Symbol(s);
}

uint prod_count = 0;
uint state_count = 0;

void make_closure(State& state) {
	bool new_items = false;
	do {
		new_items = false;
		for (const Item& i : state.items.s) {
			Symbol b = i.get();
			if (!lr.rule_map.has(b))
				continue;
			Symbol c = i.has(1) ? i.get(1) : i.lookahead;
			if (!lr.first_map.has(c))
				continue;
			for (Symbol x : lr.first_map[c].s) {
				for (Product* p : lr.rule_map[b].s) {
					//if (!lr.rtc_map.has(p))
					//	continue;
					//for (Product* q : lr.rtc_map[p].s) {
						Item j(p, x);
						if (!state.items.has(j)) {
							new_items = true;
							state.items.s.insert(j);
						}
					//}
				}
			}
		}
	} while (new_items);
}

void make_closure_fast(State& state) {
	Items new_items;
	for (const Item& i : state.items.s) {
		new_items.s.insert(i);
		Symbol b = i.get(0);
		if (!lr.rule_map.has(b))
			continue;
		Symbol c = i.has(1) ? i.get(1) : i.lookahead;
		if (!lr.first_map.has(c))
			continue;
		for (Symbol x : lr.first_map[c].s) {
			for (Product* p : lr.rule_map[b].s) {
				if (!lr.rtc_map.has(p))
					continue;
				for (Product* q : lr.rtc_map[p].s) {
					new_items.s.insert(Item(q, x));
				}
				/*for (Product* q : lr.prod_vect) {
					if (lr.rtc_map_1[p][q]) {
						new_items.s.insert(Item(q, x));
					}
				}*/
			}
		}
	}
	state.items = new_items;
}

inline bool diff_items (const Item& i1, const Item& i2) {
	return !(i1.prod == i2.prod && i1.lookahead == i2.lookahead && i1.dot == i2.dot);
}

bool diff_states (const State& s1, const State& s2) {
	if (s1.items.s.size() != s2.items.s.size())
		return true;
	for (auto i : s1.items.s) {
		if (s2.items.s.find(i) == s2.items.s.end())
			return true;
	}
	return false;
}

string show_diff(const State& s1, const State& s2) {
	string str;
	str += "s1\\s2 = {\n";
	int c = 0;
	for (auto i : s1.items.s) {
		if (s2.items.s.find(i) == s2.items.s.end()) {
			str += "\t" + show(i) + ",\n";
			if ((++ c) > 10)
				break;
		}
	}
	str += "}\n";
	str += "s2\\s1 = {\n";
	c = 0;
	for (auto i : s2.items.s) {
		if (s1.items.s.find(i) == s1.items.s.end()) {
			str += "\t" + show(i) + ",\n";
			if ((++ c) > 10)
				break;
		}
	}
	str += "}\n";
	return str;
}

State make_goto(const State& from, Symbol X) {
	State to;
	to.ind = -1;
	for (Item it : from.items.s) {
		if (it.has() && it.get() == X) {
			it.dot += 1;
			to.items.s.insert(it);
		}
	}
	make_closure(to);
	/*State x = to;
	State y = to;
	State z = to;
	State a = to;
	make_closure(to);
	make_closure_fast(x);
	if (diff_states(to, x)) {
		cout << endl;
		cout << "orig item:" << endl;
		cout << show(a) << endl;
		cout << "diff closures:" << endl;
		cout << show_diff(to, x) << endl;
		cout << show_grammar() << endl;
		cout << "to = " << to.items.s.size() << endl;
		cout << show(to) << endl;
		cout << "x  = " << x.items.s.size() << endl;
		cout << show(x)  << endl;
		make_closure(y);
		make_closure_fast(z);
		throw Error("fuck off");
	}*/
	return to;
}

struct StateSymb {
	State* state;
	Symbol symb;
};

struct LessStateSymb {
	bool operator () (const StateSymb& s1, const StateSymb& s2) const {
		static Less<State*> less;
			 if (less(s1.state, s2.state)) return true;
		else if (less(s2.state, s1.state)) return false;
		else return s1.symb < s2.symb;
	}
};

void collect_states() {
	bool new_state = false;
	Set<StateSymb, LessStateSymb> visited;
	do {
		new_state = false;
		for (State* from : lr.state_set.s) {
			for (Symbol x : lr.symbol_set.s) {
				/*if (visited.has(StateSymb {from, x}))
					continue;
				else
					visited.s.insert(StateSymb {from, x});*/

				State t = make_goto(*from, x);
				if (t.items.s.empty())
					continue;
				State* to = nullptr;
				if (!lr.state_set.has(&t)) {
					to = new State(t);
					to->ind = state_count++;
					lr.state_vect.push_back(to);
					lr.state_set.s.insert(to);
					new_state = true;
					lr.goto_map[from][x] = to;
				} else {
					to = *lr.state_set.s.find(&t);
				}
				lr.goto_map[from][x] = to;
			}
		}
	} while (new_state);
}

Action construct_action(const Item& i, Symbol x, State* to) {
	Action act;
	if (i.completed() && i.lookahead == x) {
		if (i.prod->kind == Product::INIT) {
			if (x == end_marker())
				act.kind = Action::ACCEPT;
		} else
			act.kind = Action::REDUCE;
		act.val.prod = i.prod;
	} else if (to && i.get() == x) {
		act.kind = Action::SHIFT;
		act.val.state = to;
	}
	return act;
}

void complement_tables(State* from, Symbol x, State* to, Table& table) {
	if (is_non_term(x) && to) {
		table.gotos[from][x] = to;
	} else {
		for (auto& i : from->items.s) {
			Action act = construct_action(i, x, to);
			if (act.kind != Action::NONE)
				table.actions[from][x].s.insert(act);
		}
	}
}


void create_tables(Table& table) {
	for (State* from : lr.state_set.s) {
		for (Symbol x : lr.symbol_set.s) {
			State* to = lr.goto_map.has(from) ? (lr.goto_map[from].has(x) ? lr.goto_map[from][x] : nullptr) : nullptr;
			complement_tables(from, x, to, table);
		}
	}
}


void add_first(Product* prod) {
	Symbol s = prod->right[0];
	if (is_terminal(s))
		lr.first_map[prod->left].s.insert(s);
	else
		lr.first_map[prod->left].s.insert(lr.first_map[s].s.begin(), lr.first_map[s].s.end());

	for (Symbol s : prod->right) {
		if (is_terminal(s))
			lr.first_map[s].s.insert(s);
	}
	for (Product* p : lr.prod_vect) {
		if (p == prod)
			continue;
		Symbol x = p->right[0];
		if (is_non_term(x) && x == prod->left)
			lr.first_map[p->left].s.insert(lr.first_map[prod->left].s.begin(), lr.first_map[prod->left].s.end());
	}
}

void add_follow(Product* prod) {
	for (uint i = 0; i < prod->right.size(); ++ i) {
		Symbol s = prod->right[i];
		if (is_non_term(s)) {
			if (i + 1 < prod->right.size()) {
				Symbol x = prod->right[i + 1];
				if (lr.first_map.has(x)) {
					lr.follow_map[s].s.insert(lr.first_map[x].s.begin(), lr.first_map[x].s.end());
				}
			} else if (lr.follow_map.has(prod->left)) {
				lr.follow_map[s].s.insert(lr.follow_map[prod->left].s.begin(), lr.follow_map[prod->left].s.end());
			}
		}
	}
}


void check_prod(Product* prod) {
	if (!lr.non_terminals.has(prod->left))
		throw Error("undefined type ", expr::show(prod->left));
	for (Symbol s : prod->right)
		if (!lr.symbol_set.has(s))
			throw Error("undefined symbol ", expr::show(s));
}


void add_init_states(Table& table) {
	for (auto p : lr.init_map.m) {
		Product* prod = p.second;

		Item it(prod, end_marker());
		State* init = new State;
		init->ind = state_count ++ ;
		init->items.s.insert(it);
		make_closure(*init);

		lr.state_set.s.insert(init);
		lr.state_vect.push_back(init);

		table.inits[prod->left.type] = init;
	}
}


void make_RTC() {
	for (Product* p : lr.prod_vect) {
		for (Product* q : lr.prod_vect) {
			if (lr.rtc_map[p].has(q)) {
				for (Product* r : lr.rtc_map[q].s) {
					lr.rtc_map[p].s.insert(r);
				}
			}
		}
	}
}


bool check_RTC_1() {
	bool correct = true;
	for (Product* p : lr.prod_vect) {
		for (Product* q : lr.prod_vect) {
			for (Product* r : lr.prod_vect) {
				if (lr.rtc_map_1[p][q] && lr.rtc_map_1[q][r] && !lr.rtc_map_1[p][r]) {
					cout << endl;
					cout << "RTC ERROR: has [p][q], [q][r] but don't have [p][r]" << endl;
					cout << "p = " << show(*p) << endl;
					cout << "q = " << show(*q) << endl;
					cout << "r = " << show(*r) << endl;
					correct = false;
				}
			}
		}
	}
	return correct;
}


void make_RTC_1() {
	for (Product* p : lr.prod_vect) {
		for (Product* q : lr.prod_vect) {
			lr.rtc_map_1[p][q] = (p == q) || (q->left == p->right[0]);
		}
	}
	for (Product* q : lr.prod_vect) {
		for (Product* p : lr.prod_vect) {
			if (lr.rtc_map_1[p][q]) {
				for (Product* r : lr.prod_vect) {
					lr.rtc_map_1[p][r] = lr.rtc_map_1[p][r] || lr.rtc_map_1[q][r];
				}
			}
		}
	}
	if (!check_RTC_1()) {
		cout << "RTC_1 IS NOT CORRECT" << endl;
	} else {
		cout << "RTC_1 IS CORRECT" << endl;
	}
	for (Product* p : lr.prod_vect) {
		for (Product* q : lr.prod_vect) {
			if (lr.rtc_map_1[p][q]) {
				lr.rtc_map[p].s.insert(q);
			}
		}
	}
	bool correct = true;
	for (Product* p : lr.prod_vect) {
		for (Product* q : lr.prod_vect) {
			if (lr.rtc_map_1[p][q] != lr.rtc_map[p].has(q)) {
				correct = false;
			}
		}
	}
	if (!correct) {
		cout << "RTC IS NOT CORRECT" << endl;
	} else {
		cout << "RTC IS CORRECT" << endl;
	}
}

void make_iRTC_1() {
	for (Product* p : lr.prod_vect) {
		for (Product* q : lr.prod_vect) {
			lr.rtc_map_1[p][q] = (p == q) || (q->left == p->right[0]);
		}
	}
	for (Product* q : lr.prod_vect) {
		for (Product* p : lr.prod_vect) {
			if (lr.rtc_map_1[p][q]) {
				for (Product* r : lr.prod_vect) {
					lr.rtc_map_1[p][r] = lr.rtc_map_1[p][r] || lr.rtc_map_1[q][r];
				}
			}
		}
	}
	if (!check_RTC_1()) {
		cout << "RTC_1 IS NOT CORRECT" << endl;
	} else {
		cout << "RTC_1 IS CORRECT" << endl;
	}
	for (Product* p : lr.prod_vect) {
		for (Product* q : lr.prod_vect) {
			if (lr.rtc_map_1[p][q]) {
				lr.rtc_map[p].s.insert(q);
			}
		}
	}
	bool correct = true;
	for (Product* p : lr.prod_vect) {
		for (Product* q : lr.prod_vect) {
			if (lr.rtc_map_1[p][q] != lr.rtc_map[p].has(q)) {
				correct = false;
			}
		}
	}
	if (!correct) {
		cout << "RTC IS NOT CORRECT" << endl;
	} else {
		cout << "RTC IS CORRECT" << endl;
	}
}

string show_RTC() {
	string str("RTC:\n");
	for (auto pp : lr.rtc_map.m) {
		Product* p = pp.first;
		if (pp.second.s.empty()) {
			//str += "\t" + show(*p) + " -> ";
			//str += "EMPTY\n";
		} else if (pp.second.s.size() == 1) {
			//str += "\t" + show(*p) + " -> ";
			//str += "SINGULAR\n";
		} else {
			str += "\t" + show(*p) + " -> ";
			str += "{\n";
			for (Product* q : pp.second.s) {
				str += "\t\t" + show(*q) + ",\n";
			}
			str += "\n\t}\n";
		}
	}
	return str;
}

Table create_table() {
	Table table;
	Timer t;

	/*
	t.start();
	cout << endl << "making reflexive transitive closure ... " << endl;
	//make_RTC();
	make_RTC_1();
	cout << show_RTC();
	t.stop();
	cout << "done in " << t << endl;
	//cout << show_grammar() << endl;
	//cout << show_RTC() << endl;
	 *
	 */

	cout << endl << "init states ... " << flush;
	t.start();
	add_init_states(table);
	t.stop();
	cout << "done in " << t << endl;

	cout << endl << "collect states ... " << flush;
	t.start();
	collect_states();
	t.stop();
	cout << "done in " << t << endl;

	cout << endl << "creating tables ... " << flush;
	t.start();
	create_tables(table);
	t.stop();
	cout << "done in " << t << endl;

	table.vars = lr.var_map;
	return table;
}

void add_product(Product* prod) {
	check_prod(prod);

	lr.prod_vect.push_back(prod);
	lr.rule_map[prod->left].s.insert(prod);

	add_first(prod);
	lr.rtc_map[prod].s.insert(prod);
	for (Product* p : lr.prod_vect) {
		add_follow(p);

		if (p->left == prod->right[0])
			lr.rtc_map[prod].s.insert(p);
		else if (prod->left == p->right[0])
			lr.rtc_map[p].s.insert(prod);
	}
}

void add_var_product(Symbol s, Symbol s_) {
	Product* prod = new Product(s, s_, Product::VAR);
	add_product(prod);
}

void add_init_product(Symbol _s, Symbol s) {
	Product* prod = new Product(_s, s, Product::INIT);
	lr.init_map[s.type] = prod;
	add_product(prod);
}

} // anonymous namespace

string show_lr() {
	string str;
	//str += show(table());
	str += show(lr);
	return str;
}

string Table::show() const {
	string str;
	str += "Parsing tables statistics:\n";
	str += "  states : " + to_string(actions.m.size()) + "\n";
	uint act_count = 0;
	for (auto p : actions.m)
		act_count += p.second.m.size();
	str += "  actions: " + to_string(act_count) + "\n";
	uint goto_count = 0;
	for (auto p : gotos.m)
		goto_count += p.second.m.size();
	str += "  gotos  : " + to_string(goto_count) + "\n";
	return str;
}

LR::~ LR() {
	for (State* s : state_vect) delete s;
	for (Product* p : prod_vect) delete p;
}

Product::Product(rus::Rule* r, Kind k) :
left(make_non_term(r->type)), right(), kind(k), rule(r), ind(prod_count++) {
	for (auto s : r->term) {
		if (s.symb.type)
			right.push_back(make_non_term(s.symb.type));
		else
			right.push_back(s.symb);
	}
}

Product::Product(Symbol l, Symbol r, Kind k) :
left(l), right(), kind(k), rule(nullptr), ind(prod_count++) {
	right.push_back(r);
	assert(left.type);
}

Table& table() {
	static Table table = create_table();
	return table;
}

void add_rule(Rule* rule) {
	Product* prod = new Product(rule);
	add_product(prod);
}

void add_type(Type* type) {
	Symbol  s  = make_non_term(type);
	Symbol _s  = make_non_term(type, "_");
	Symbol  s_ = make_terminal(type, "_");
	if (lr.non_terminals.has(s))
		throw Error("type already declared", show_id(type->id));

	lr.non_terminals.s.insert(s);
	lr.non_terminals.s.insert(_s);
	lr.terminals.s.insert(s_);
	lr.symbol_set.s.insert(s);
	lr.symbol_set.s.insert(_s);
	lr.symbol_set.s.insert(s_);
	lr.follow_map[_s].s.insert(end_marker());
	lr.var_map[type] = s_;

	add_init_product(_s, s);
	add_var_product(s, s_);
}

void add_const(Const* c) {
	static bool first = true;
	if (first) {
		lr.terminals.s.insert(end_marker());
		lr.symbol_set.s.insert(end_marker());
		lr.first_map[end_marker()].s.insert(end_marker());
		first = false;
	}

	if (lr.terminals.has(c->symb))
		throw Error("type already declared", expr::show(c->symb));
	lr.terminals.s.insert(c->symb);
	lr.symbol_set.s.insert(c->symb);
}

}}} // namespace mdl::rus::expr

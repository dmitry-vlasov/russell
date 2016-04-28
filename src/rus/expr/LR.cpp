#include "common.hpp"
#include "rus/expr/LR.hpp"

namespace mdl { namespace rus { namespace expr {

static Symbol make_non_term(Type* t, const char* prefix = "") {
	string s = prefix;
	s += Rus::get().lex.ids.toStr(t->id);
	return Symbol(s, t);
}

static Symbol make_terminal(Type* t, const char* postfix = "") {
	string s = Rus::get().lex.ids.toStr(t->id) + postfix;
	return Symbol(s);
}

static uint prod_count = 0;

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
}

static uint state_count = 0;

LR::~ LR() {
	for (State* s : state_vect) delete s;
	for (Product* p : prod_vect) delete p;
}

LR lr;

Table& table() { return lr.table; }

void make_closure(State& state) {
	bool new_items = false;
	do {
		new_items = false;
		for (const Item& i : state.items.s) {
			Symbol b = i.get();
			if (!lr.rule_map.has(b))
				continue;
			for (Product* p : lr.rule_map[b].s) {
				Symbol c = i.has(1) ? i.get(1) : i.lookahead;
				if (!lr.first_map.has(c))
					continue;
				for (Symbol x : lr.first_map[c].s) {
					Item j(p, x);
					if (!state.items.has(j)) {
						new_items = true;
						state.items.s.insert(j);
					}
				}
			}
		}
	} while (new_items);
}

Action construct_action(const Item& i, Symbol x, State* to) {
	Action act;
	if (i.completed()) {
		if (i.prod->kind == Product::INIT)
			act.kind = Action::ACCEPT;
		else
			act.kind = Action::REDUCE;
		act.val.prod = i.prod;
	} else if (is_terminal(x) && i.get() == x) {
		act.kind = Action::SHIFT;
		act.val.state = to;
	}
	return act;
}

void complement_tables(State* from, Symbol x, State* to) {
	lr.table.gotos[from][x] = to;
	Action act;
	uint c = 0;
	for (auto& i : from->items.s) {
		Action a = construct_action(i, x, to);
		if (act.kind != Action::NONE && a.kind != Action::NONE && a != act) {
			cout << endl << "conflicting actions: " << show(act) << " and " << show(a) << endl;

			cout << "ITER: " << c << endl << endl;
			cout << "FROM: " << endl << show(*from) << endl << endl;
			cout << "X: " << endl << expr::show(x) << endl << endl;
			cout << "TO: " << endl << show(*to) << endl << endl;
			cout << "ITEM: " << endl << show(i) << endl << endl;

			cout << endl << show_lr() << endl;
			throw Error("non LR(1) grammar");
		}
		act = a;
		++ c;
	}
	lr.table.actions[from][x] = act;
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
	return to;
}

void collect_states() {
	lr.table.actions.m.clear();
	lr.table.gotos.m.clear();
	bool new_state = false;
	do {
		new_state = false;
		for (State* from : lr.state_set.s) {
			for (Symbol x : lr.symbol_set.s) {
				State t = make_goto(*from, x);
				if (!t.items.s.empty() && !lr.state_set.has(&t)) {
					State* to = new State(t);
					to->ind = state_count++;
					lr.state_vect.push_back(to);
					lr.state_set.s.insert(to);
					new_state = true;
					complement_tables(from, x, to);


					//cout << show(*to) << endl;
				}
			}
		}
	} while (new_state);
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


static void check_prod(Product* prod) {
	if (!lr.non_terminals.has(prod->left))
		throw Error("undefined type ", expr::show(prod->left));
	for (Symbol s : prod->right)
		if (!lr.symbol_set.has(s))
			throw Error("undefined symbol ", expr::show(s));
}


static void remove_states() {
	for (State* s : lr.state_vect) delete s;
	lr.state_vect.clear();
	lr.state_set.s.clear();
	state_count = 0;
}

static void add_init_states() {
	for (auto p : lr.init_map.m) {
		Product* prod = p.second;

		Item it(prod, end_marker());
		State* init = new State;
		init->ind = state_count ++ ;
		init->items.s.insert(it);
		make_closure(*init);

		lr.state_set.s.insert(init);
		lr.state_vect.push_back(init);
	}
}

static void add_product(Product* prod) {
	check_prod(prod);

	lr.prod_vect.push_back(prod);
	lr.rule_map[prod->left].s.insert(prod);

	add_first(prod);
	for (Product* p : lr.prod_vect)
		add_follow(p);

	remove_states();
	add_init_states();
	collect_states();
}

static void add_term_product(Symbol s, Symbol s_) {
	Product* prod = new Product(s, s_);
	add_product(prod);
}

static void add_init_product(Symbol _s, Symbol s) {
	Product* prod = new Product(_s, s);
	lr.init_map[s.type] = prod;
	add_product(prod);
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

	add_init_product(_s, s);
	add_term_product(s, s_);
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

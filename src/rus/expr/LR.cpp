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

uint State::count = 0;

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
		for (const Item& i : state.items) {
			Symbol b = i.after_dot();
			if (!lr.rule_map.has(b))
				continue;
			for (Product* p : lr.rule_map[b].s) {
				if (!lr.follow_map.has(b))
					continue;
				for (Symbol x : lr.follow_map[b].s) {
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
				if (lr.init_prods.has(i.prod))
					act.kind = Action::ACCEPT;
				else
					act.kind = Action::REDUCE;
				act.val.prod = i.prod;
				cout << "going to be: " << show(act) << endl;
				cout << show_lr() << endl;
				throw Error("non LR(1) grammar");
			} else {
				if (lr.init_prods.has(i.prod))
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
		for (State* from : lr.state_set.s) {
			for (Symbol x : lr.symbol_set.s) {
				State t = make_goto(*from, x);
				if (!t.items.empty() && !lr.state_set.has(&t)) {
					State* to = new State(t);
					to->ind = State::count++;
					lr.state_vect.push_back(to);
					lr.state_set.s.insert(to);
					new_state = true;
					complement_tables(from, x, to);


					cout << show(*to) << endl;
				}
			}
		}
	} while (new_state);
}

void add_first(Product* prod) {
	// Arrange first:
	Symbol s = prod->right[0];
	if (is_terminal(s))
		lr.first_map[prod->left].s.insert(s);
	else
		lr.first_map[prod->left].s.insert(lr.first_map[s].s.begin(), lr.first_map[s].s.end());

	for (uint i = 0; i < prod->right.size(); ++ i) {
		Symbol s = prod->right[i];
		if (is_terminal(s))
			lr.first_map[s].s.insert(s);
	}
}

void add_follow(Product* prod) {
	// Arrange follow:
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
		throw Error("undefined type ", show(prod->left));
	for (Symbol s : prod->right)
		if (!lr.symbol_set.has(s))
			throw Error("undefined symbol ", show(s));
}

static void add_product(Product* prod) {
	check_prod(prod);

	lr.prod_vect.push_back(prod);
	lr.rule_map[prod->left].s.insert(prod);

	add_first(prod);
	for (Product* p : lr.prod_vect)
		add_follow(p);

	collect_states();
}

static void add_term_product(Symbol s, Symbol s_) {
	Product* prod = new Product(s, s_);
	add_product(prod);
}

static void add_init_product(Symbol _s, Symbol s) {
	Product* prod = new Product(_s, s);

	Item it(prod, end_marker());
	State* init = new State(State::FINAL);
	init->items.insert(it);
	make_closure(*init);

	lr.state_set.s.insert(init);
	lr.state_vect.push_back(init);
	lr.init_prods.s.insert(prod);
	lr.init_map[s.type] = init;

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

	add_init_product(_s, s);
	add_term_product(s, s_);
}

void add_const(Const* c) {
	if (lr.terminals.has(c->symb))
		throw Error("type already declared", show(c->symb));
	lr.terminals.s.insert(c->symb);
	lr.symbol_set.s.insert(c->symb);
}


}}} // namespace mdl::rus::expr

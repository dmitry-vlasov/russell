#include "common.hpp"
#include "rus/expr/LR.hpp"

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

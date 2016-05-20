#include <boost/range/adaptor/reversed.hpp>
#include "rus/expr/table.hpp"
#include "rus/expr/LR.hpp"

namespace mdl { namespace rus { namespace expr { namespace {

typedef Expr::Node Node;
typedef Term<Node> Term;

struct Unit {
	State* state;
	Term*  term;
	Node*  node;
	Unit*  prev;
};

vector<Expr*> queue;

void show_stack(vector<Unit>& stack, Node* n) {
	cout << "\t";
	for (Unit& u : stack) {
		cout << u.state->ind << " ";
		if (u.term)
			cout << show_ast(u.term, true);
		else
			cout << " ";
	}
	cout << " -- ";
	if (!n) {
		cout << "<end>";
	} else {
		while (n) {
			cout << expr::show(n->symb) << " ";
			n = n->next;
		}
	}
}

void add_terms(Term* term) {
	for (auto t : term->children)
		add_terms(t);
	term->first->init.push_back(term);
	term->last->final.push_back(term);
}

inline Symbol current(Node* n) {
	return n ? n->symb : end_marker();
}

void parse(Expr* ex, bool trace = false) {
	Node* n = ex->first;
	vector<Unit> stack;
	Table& tab = table();
	if (!tab.inits.has(ex->type)) {
		string msg("expression doesn't have a valid start non-terminal.\n");
		msg += string("expression: ") + show(*ex) + "\n";
		msg += show_grammar();
		throw Error("expression syntax error (0): ", msg);
	}
	State* init = tab.inits[ex->type];
	stack.push_back(Unit{init, nullptr, n, nullptr});
	bool end = false;
	while (!end) {
		if (trace)
			show_stack(stack, n);
		Unit u = stack.back();
		if (!tab.actions.has(u.state)) {
			string msg("actions table doesn't have a state.\n");
			msg += string("state: ") + to_string(u.state->ind) + "\n";
			msg += string("expression: ") + show(*ex) + "\n";
			msg += show_grammar();
			throw Error("expression syntax error (1): ", msg);
		}
		Symbol x = current(n);
		if (x.type && !tab.vars.has(x.type)) {
			string msg("variable table doesn't have a variable of type.\n");
			msg += string("type: ") + show_id(x.type->id) + "\n";
			msg += string("expression: ") + show(*ex) + "\n";
			msg += show_grammar();
			throw Error("expression syntax error (2): ", msg);
		}
		Symbol s = x.type ? tab.vars[x.type] : x;
		if (!tab.actions[u.state].has(s)) {
			string msg("action table doesn't have a symbol.\n");
			msg += string("symbol: ") + expr::show(s, false) + "\n";
			msg += string("expression: ") + show(*ex) + "\n";
			msg += show_grammar();
			msg += "actions:\n";
			//for (auto p : tab.actions[u.state].m)
			//	msg += "\t" + expr::show(p.first) + " --> " + show(p.second) + "\n";
			throw Error("expression syntax error (3): ", msg);
		}
		Action act = *tab.actions[u.state][s].s.begin();
		if (trace)
			cout << "            " << show(act) << endl;
		switch (act.kind) {
		case Action::SHIFT:
			if (!n) {
				string msg("shift is impossible.\n");
				msg += string("expression: ") + show(*ex) + "\n";
				msg += show_grammar();
				throw Error("expression syntax error (4): ", msg);
			}
			stack.push_back(Unit{act.val.state, nullptr, n, &u});
			n = n->next;
			break;
		case Action::REDUCE: {
			Unit w = u;
			vector<Term*> terms;
			for (uint i = 0; i < act.val.prod->right.size(); ++ i) {
				if (w.term)
					terms.push_back(w.term);
				stack.pop_back();
				w = stack.back();
			}
			std::reverse(terms.begin(), terms.end());
			if (!tab.gotos.has(w.state)) {
				string msg("goto table doesn't have a state.\n");
				msg += string("state: ") + to_string(u.state->ind) + "\n";
				msg += string("expression: ") + show(*ex) + "\n";
				msg += show_grammar();
				throw Error("expression syntax error (5): ", msg);
			}
			if (!tab.gotos[w.state].has(act.val.prod->left)) {
				string msg("goto table doesn't have a symbol.\n");
				msg += string("symbol: ") + expr::show(act.val.prod->left, false) + "\n";
				msg += string("expression: ") + show(*ex) + "\n";
				msg += show_grammar();
				throw Error("expression syntax error (6): ", msg);
			}
			State* s = tab.gotos[w.state][act.val.prod->left];
			Term*  t = nullptr;
			if (act.val.prod->kind == Product::VAR) {
				//assert(u.node == n ||
				//	(u.node->next == n && n->symb == end_marker()));
				assert(terms.size() == 0);
				assert(!act.val.prod->rule);
				t = new Term(u.node);
			} else {
				assert(act.val.prod->rule);
				t = new Term(w.node, (n ? n : ex->last), act.val.prod->rule, terms);
			}
			stack.push_back(Unit{s, t, n});
		}	break;
		case Action::ACCEPT:
			assert(!n);
			add_terms(u.term);
			stack.pop_back();
			assert(stack.back().state == init);
			assert(!n);
			end = true;
			break;
		default:
			assert(false && "Impossible");
		}
	}
	//cout << endl;
	//cout << "expr: " << show(*ex) << endl;
	//cout << "AST: " << show_ast(*ex) << endl;
	//cout << endl;
}

/*struct Stack {
	Unit unit;
	Stack* prev;
	vector<Stack> next;
	Stack(Unit u, Stack* p = nullptr) :
		unit(u), prev(p), next() {
	}

	void push(Unit unit) {
		next.push_back(Stack(unit, this));
	}
	Unit pop() {
		Unit
	}
};*/


bool parse_GLR(Table& tab, Expr* ex, Node* n, Unit u) {
	//if (trace)
	//	show_stack(stack, n);

	if (!tab.actions.has(u.state)) {
		string msg("actions table doesn't have a state.\n");
		msg += string("state: ") + to_string(u.state->ind) + "\n";
		msg += string("expression: ") + show(*ex) + "\n";
		msg += show_grammar();
		throw Error("expression syntax error (1): ", msg);
	}
	Symbol x = current(n);
	if (x.type && !tab.vars.has(x.type)) {
		string msg("variable table doesn't have a variable of type.\n");
		msg += string("type: ") + show_id(x.type->id) + "\n";
		msg += string("expression: ") + show(*ex) + "\n";
		msg += show_grammar();
		throw Error("expression syntax error (2): ", msg);
	}
	Symbol s = x.type ? tab.vars[x.type] : x;
	if (!tab.actions[u.state].has(s)) {
		string msg("action table doesn't have a symbol.\n");
		msg += string("symbol: ") + expr::show(s, false) + "\n";
		msg += string("expression: ") + show(*ex) + "\n";
		msg += show_grammar();
		msg += "actions:\n";
		//for (auto p : tab.actions[u.state].m)
		//	msg += "\t" + expr::show(p.first) + " --> " + show(p.second) + "\n";
		throw Error("expression syntax error (3): ", msg);
	}
	for (Action act : tab.actions[u.state][s].s) {
		//if (trace)
		//	cout << "            " << show(act) << endl;
		switch (act.kind) {
		case Action::SHIFT:
			if (!n) {
				string msg("shift is impossible.\n");
				msg += string("expression: ") + show(*ex) + "\n";
				msg += show_grammar();
				throw Error("expression syntax error (4): ", msg);
			}
			//stack.push_back(Unit{act.val.state, nullptr, n});
			//n = n->next;
			if (parse_GLR(tab, ex, n->next, Unit{act.val.state, nullptr, n, &u}))
				return true;
			break;
		case Action::REDUCE: {
			Unit w = u;
			vector<Term*> terms;
			for (uint i = 0; i < act.val.prod->right.size(); ++ i) {
				if (w.term)
					terms.push_back(w.term);
				assert(w.prev);
				w = *w.prev;
				//stack.pop_back();
				//w = stack.back();
			}
			std::reverse(terms.begin(), terms.end());
			if (!tab.gotos.has(w.state)) {
				string msg("goto table doesn't have a state.\n");
				msg += string("state: ") + to_string(u.state->ind) + "\n";
				msg += string("expression: ") + show(*ex) + "\n";
				msg += show_grammar();
				throw Error("expression syntax error (5): ", msg);
			}
			if (!tab.gotos[w.state].has(act.val.prod->left)) {
				string msg("goto table doesn't have a symbol.\n");
				msg += string("symbol: ") + expr::show(act.val.prod->left, false) + "\n";
				msg += string("expression: ") + show(*ex) + "\n";
				msg += show_grammar();
				throw Error("expression syntax error (6): ", msg);
			}
			State* s = tab.gotos[w.state][act.val.prod->left];
			Term*  t = nullptr;
			if (act.val.prod->kind == Product::VAR) {
				//assert(u.node == n ||
				//	(u.node->next == n && n->symb == end_marker()));
				assert(terms.size() == 0);
				assert(!act.val.prod->rule);
				t = new Term(u.node);
			} else {
				assert(act.val.prod->rule);
				t = new Term(w.node, (n ? n : ex->last), act.val.prod->rule, terms);
			}
			parse_GLR(tab, ex, n, Unit{s, t, n, &w});
		}	break;
		case Action::ACCEPT:
			assert(!n);
			add_terms(u.term);
			//assert(!u.prev);
			//stack.pop_back();
			//assert(u.state == init);
			assert(!n);
			return true;
			break;
		default:
			assert(false && "Impossible");
		}
	}
	return false;
}

void parse_GLR(Expr* ex, bool trace = false) {
	Node* n = ex->first;
	Table& tab = table();
	if (!tab.inits.has(ex->type)) {
		string msg("expression doesn't have a valid start non-terminal.\n");
		msg += string("expression: ") + show(*ex) + "\n";
		msg += show_grammar();
		throw Error("expression syntax error (0): ", msg);
	}
	State* init = tab.inits[ex->type];
	//Stack stack(Unit{init, nullptr, n});
	parse_GLR(tab, ex, n, Unit{init, nullptr, n, nullptr});
}


} // anonymous namespace

void enqueue(Expr& ex) {
	queue.push_back(&ex);
}

void parse() {
	//cout << endl << show_lr() << endl;
	Timer t;
	t.start();
	cout << endl << "making table ... " << endl;
	cout << table().show() << endl;
	t.stop();
	cout << "done in " << t << endl;
	cout << show_grammar() << endl;
	uint c = 0;
	for (Expr* ex : queue) {
		try {
			parse_GLR(ex);
			c += 1;
		} catch (Error& err) {
			cout << endl;
			cout << "expression no.: " << c << endl;
			parse(ex, true);
			cout << err.what() << endl;
			throw err;
		}
	}
	queue.clear();
}

}}} // namespace mdl::rus::expr

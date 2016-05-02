#include <boost/range/adaptor/reversed.hpp>
#include "rus/expr/table.hpp"
#include "rus/expr/LR.hpp"

namespace mdl { namespace rus { namespace expr {

typedef Expr::Node Node;
typedef Term<Node> Term;

struct Unit {
	State* state;
	Term*  term;
	Node*  node;
};

static vector<Expr*> queue;

void show_stack(vector<Unit>& stack, Node* n) {
	cout << "\t";
	for (Unit& u : stack) {
		cout << u.state->ind << " ";
		if (u.term)
			cout << "<" << show_ast(u.term) << "> ";
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
	cout << endl;
}

void add_terms(Term* term) {
	for (auto t : term->children) add_terms(t);
	term->first->init.push_back(term);
	term->last->final.push_back(term);
}

Symbol current(Node* n) {
	return n ? n->symb : end_marker();
}

static void parse(Expr& ex) {
	Node* n = ex.first;
	vector<Unit> stack;
	Table& tab = table();
	if (!tab.inits.has(ex.type))
		throw Error("expression syntax error: ", show(ex));
	State* init = tab.inits[ex.type];
	stack.push_back(Unit{init, nullptr, n});
	while (true) {
		show_stack(stack, n);
		Unit u = stack.back();
		if (!tab.actions.has(u.state))
			throw Error("expression syntax error: ", show(ex));
		Symbol x = current(n);
		Symbol s = x.type ? tab.vars[x.type] : x;
		if (s.type && !tab.vars.has(s.type))
			throw Error("expression syntax error: ", show(ex));
		if (!tab.actions[u.state].has(s))
			throw Error("expression syntax error: ", show(ex));
		Action act = tab.actions[u.state][s];
		switch (act.kind) {
		case Action::SHIFT:
			if (!n)
				throw Error("expression syntax error: ", show(ex));
			stack.push_back(Unit{act.val.state, nullptr, n});
			n = n->next;
			break;
		case Action::REDUCE: {
			Unit w = u;
			vector<Term*> terms;
			for (Symbol s : boost::adaptors::reverse(act.val.prod->right)) {
				//assert(s == stack.top().state.);
				if (w.term)
					terms.push_back(u.term);
				stack.pop_back();
				w = stack.back();
			}
			if (!tab.gotos.has(w.state))
				throw Error("expression syntax error: ", show(ex));
			if (!tab.gotos[w.state].has(act.val.prod->left))
				throw Error("expression syntax error: ", show(ex));
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
				t = new Term(w.node, (n ? n : ex.last), act.val.prod->rule, terms);
			}
			stack.push_back(Unit{s, t, n});
		}	break;
		case Action::ACCEPT:
			assert(!n);
			add_terms(u.term);
			stack.pop_back();
			assert(stack.back().state == init);
			assert(!n);
			goto end;
			break;
		default:
			assert(false && "Impossible");
		}
	}
	end :
	cout << endl << "AST:\n" << show_ast(ex) << endl;
}


void enqueue(Expr& ex) {
	queue.push_back(&ex);
}

void parse() {
	cout << endl << show_lr() << endl;
	for (Expr* ex : queue)
		parse(*ex);
	queue.clear();
}

}}} // namespace mdl::rus::expr

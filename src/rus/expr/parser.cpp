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
};

vector<Expr*> queue;

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
	if (!tab.inits.has(ex->type))
		throw Error("expression syntax error (0): ", show(*ex));
	State* init = tab.inits[ex->type];
	stack.push_back(Unit{init, nullptr, n});
	bool end = false;
	while (!end) {
		if (trace)
			show_stack(stack, n);
		Unit u = stack.back();
		if (!tab.actions.has(u.state))
			throw Error("expression syntax error (1): ", show(*ex));
		Symbol x = current(n);
		Symbol s = x.type ? tab.vars[x.type] : x;
		if (s.type && !tab.vars.has(s.type))
			throw Error("expression syntax error (2): ", show(*ex));
		if (!tab.actions[u.state].has(s))
			throw Error("expression syntax error (3): ", show(*ex));
		Action act = tab.actions[u.state][s];
		if (trace)
			cout << "            " << show(act) << endl;
		switch (act.kind) {
		case Action::SHIFT:
			if (!n)
				throw Error("expression syntax error (4): ", show(*ex));
			stack.push_back(Unit{act.val.state, nullptr, n});
			n = n->next;
			break;
		case Action::REDUCE: {
			Unit w = u;
			vector<Term*> terms;
			//for (Symbol s : boost::adaptors::reverse(act.val.prod->right)) {
			for (uint i = 0; i < act.val.prod->right.size(); ++ i) {
				if (w.term)
					terms.push_back(w.term);
				stack.pop_back();
				w = stack.back();
			}
			if (!tab.gotos.has(w.state))
				throw Error("expression syntax error (5): ", show(*ex));
			if (!tab.gotos[w.state].has(act.val.prod->left))
				throw Error("expression syntax error (6): ", show(*ex));
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
	//cout << endl << "AST:\n" << show_ast(*ex) << endl;
}

} // anonymous namespace

void enqueue(Expr& ex) {
	queue.push_back(&ex);
}

void parse() {
	//cout << endl << show_lr() << endl;
	cout << endl << "making table" << endl;
	cout << table().show() << endl;
	for (Expr* ex : queue) {
		try {
			parse(ex);
		} catch (Error& err) {
			parse(ex, true);
			cout << endl << err.what() << endl;
			throw err;
		}
	}
	queue.clear();
}

}}} // namespace mdl::rus::expr

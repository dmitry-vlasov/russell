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
	}
	cout << " -- ";
	while (n) {
		cout << expr::show(n->symb) << " ";
		n = n->next;
	}
	cout << endl;
}

static void parse(Expr& ex) {
	Node* n = ex.first;
	vector<Unit> stack;
	if (!table().inits.has(ex.type))
		throw Error("expression syntax error: ", show(ex));
	State* init = table().inits[ex.type];
	stack.push_back(Unit{init, nullptr, nullptr});
	while (n) {
		show_stack(stack, n);
		Unit u = stack.back();
		if (!table().actions.has(u.state))
			throw Error("expression syntax error: ", show(ex));
		if (!table().actions[u.state].has(n->symb))
			throw Error("expression syntax error: ", show(ex));
		Action act = table().actions[u.state][n->symb];
		switch (act.kind) {
		case Action::SHIFT:
			stack.push_back(Unit{act.val.state, n->symb.type ? new Term(n) : nullptr, n});
			n = n->next;
			break;
		case Action::REDUCE: {
			vector<Term*> terms(act.val.prod->right.size());
			for (Symbol s : boost::adaptors::reverse(act.val.prod->right)) {
				//assert(s == stack.top().state.);
				terms.push_back(stack.back().term);
				stack.pop_back();
			}
			State* s = table().gotos[stack.back().state][act.val.prod->left];
			Term*  t = new Term(stack.back().node, n, act.val.prod->rule, terms);
			stack.push_back(Unit{s, t, n});
		}	break;
		case Action::ACCEPT:
			n = n->next;
			assert(stack.back().state == init);
			assert(!n);
			break;
		default:
			assert(false && "Impossible");
		}
	}
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

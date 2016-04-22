#include <boost/range/adaptor/reversed.hpp>
#include "rus/expr_grammar.hpp"

namespace mdl { namespace rus { namespace expr {

typedef Expr::Node Node;
typedef Term<Node> Term;

struct Unit {
	State* state;
	Term*  term;
	Node*  node;
};

void parse(Expr& ex) {
	Node* n = ex.first;
	stack<Unit> stack;
	State* init = table().inits[ex.type];
	stack.push(Unit{init, nullptr, nullptr});
	while (n) {
		Unit u = stack.top();
		Action act = table().actions[u.state][n->symb];
		switch (act.kind) {
		case Action::SHIFT:
			stack.push(Unit{act.val.state, n->symb.type ? new Term(n) : nullptr, n});
			n = n->next;
			break;
		case Action::REDUCE: {
			vector<Term*> terms(act.val.prod->right.size());
			for (Symbol s : boost::adaptors::reverse(act.val.prod->right)) {
				//assert(s == stack.top().state.);
				terms.push_back(stack.top().term);
				stack.pop();
			}
			State* s = table().gotos[stack.top().state][act.val.prod->left];
			Term*  t = new Term(stack.top().node, n, act.val.prod->rule, terms);
			stack.push(Unit{s, t, n});
		}	break;
		case Action::ACCEPT:
			n = n->next;
			assert(stack.top().state == init);
			assert(!n);
			break;
		case Action::ERROR:
			throw Error("expression syntax error: ", show(ex));
		}
	}
}


}}} // namespace mdl::rus::expr
//#include <boost/range/adaptor/reversed.hpp>

#include "GLR.hpp"
#include "rus/expr/table.hpp"

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

/*void show_stack(vector<Unit>& stack, Node* n) {
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
}*/

void add_terms(Term* term) {
	for (auto t : term->children)
		add_terms(t);
	term->first->init.push_back(term);
	term->last->final.push_back(term);
}

inline Symbol current(Node* n) {
	return n ? n->symb : end_marker();
}

bool parse_GLR(Table& tab, Expr* ex, Node* n, Unit u) {
	if (!tab.actions.has(u.state)) {
		return false;
		/*string msg("actions table doesn't have a state.\n");
		msg += string("state: ") + to_string(u.state->ind) + "\n";
		msg += string("expression: ") + show(*ex) + "\n";
		msg += show_grammar();
		throw Error("expression syntax error (1): ", msg);*/
	}
	Symbol x = current(n);
	if (x.type && !tab.vars.has(x.type)) {
		return false;
		/*string msg("variable table doesn't have a variable of type.\n");
		msg += string("type: ") + show_id(x.type->id) + "\n";
		msg += string("expression: ") + show(*ex) + "\n";
		msg += show_grammar();
		throw Error("expression syntax error (2): ", msg);*/
	}
	Symbol s = x.type ? tab.vars[x.type] : x;
	if (!tab.actions[u.state].has(s)) {
		return false;
		/*string msg("action table doesn't have a symbol.\n");
		msg += string("symbol: ") + expr::show(s, false) + "\n";
		msg += string("expression: ") + show(*ex) + "\n";
		msg += show_grammar();
		msg += "actions:\n";
		throw Error("expression syntax error (3): ", msg);*/
	}
	for (Action act : tab.actions[u.state][s].s) {
		//if (trace)
		//	cout << "            " << show(act) << endl;
		switch (act.kind) {
		case Action::SHIFT:
			if (!n) {
				break;
				/*string msg("shift is impossible.\n");
				msg += string("expression: ") + show(*ex) + "\n";
				msg += show_grammar();
				throw Error("expression syntax error (4): ", msg);*/
			}
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
			}
			std::reverse(terms.begin(), terms.end());
			if (!tab.gotos.has(w.state)) {
				break;
				/*string msg("goto table doesn't have a state.\n");
				msg += string("state: ") + to_string(u.state->ind) + "\n";
				msg += string("expression: ") + show(*ex) + "\n";
				msg += show_grammar();
				throw Error("expression syntax error (5): ", msg);*/
			}
			if (!tab.gotos[w.state].has(act.val.prod->left)) {
				break;
				/*string msg("goto table doesn't have a symbol.\n");
				msg += string("symbol: ") + expr::show(act.val.prod->left, false) + "\n";
				msg += string("expression: ") + show(*ex) + "\n";
				msg += show_grammar();
				throw Error("expression syntax error (6): ", msg);*/
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
			if (parse_GLR(tab, ex, n, Unit{s, t, n, &w}))
				return true;
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

bool parse_GLR(Expr* ex, bool trace = false) {
	Node* n = ex->first;
	Table& tab = table();
	if (!tab.inits.has(ex->type)) {
		return false;
		/*string msg("expression doesn't have a valid start non-terminal.\n");
		msg += string("expression: ") + show(*ex) + "\n";
		msg += show_grammar();
		throw Error("expression syntax error (0): ", msg);*/
	}
	State* init = tab.inits[ex->type];
	return parse_GLR(tab, ex, n, Unit{init, nullptr, n, nullptr});
}

inline Rule* find_super(Type* type, Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second;
	else
		return nullptr;
}

Term* parse_LL(Node* x, Type* type) {
	if (x->symb.type){
		if (x->symb.type == type)
			return new Term(x);
		else if (Rule* super = find_super(x->symb.type, type))
			return new Term(x, super);
	}
	if (!type->rules.root) return nullptr;
	vector<Term*> children;
	Expr::Node* f = x;

	stack<Tree<Rule*>::Node*> n;
	stack<Expr::Node*> m;
	n.push(type->rules.root);
	m.push(x);

	while (!n.empty() && !m.empty()) {
		if (Type* tp = n.top()->symb.type) {
			if (Term* child = parse_LL(m.top(), tp)) {
				children.push_back(child);
				m.top() = child->last;
				if (!n.top()->next)
					return new Term(f, m.top(), n.top()->data, children);
				else if (!m.top()->next)
					goto end;
				else {
					n.push(n.top()->next);
					m.push(m.top()->next);
				}
				continue;
			}
		} else if (n.top()->symb == m.top()->symb) {
			if (!n.top()->next)
				return new Term(f, m.top(), n.top()->data, children);
			else if (!m.top()->next)
				goto end;
			else {
				n.push(n.top()->next);
				m.push(m.top()->next);
			}
			continue;
		}
		while (!n.top()->side) {
			n.pop();
			m.pop();
			if (n.empty() || m.empty()) goto end;
		}
		n.top() = n.top()->side;
	}
	end:
	for (auto t : children) delete t;
	return nullptr;
}


bool parse_LL(Expr* ex){
	if (Term* term = parse_LL(ex->first, ex->type)) {
		add_terms(term);
		return true;
	} else {
		//trace = true;
		//parse_term(ex.first, ex.type);
		//throw Error("error at parsing", show(ex));
		return false;
	}
}


bool parse_LR() {
	Timer t;
	t.start();
	cout << "creating LR parsing tables ... " << endl;
	cout << table().show();
	t.stop();
	cout << "done in " << t << endl;
	//cout << show_grammar() << endl;
	uint c = 0;
	bool ret = true;
	t.start();
	cout << "parsing with LR ... " << flush;
	for (Expr* ex : queue) {
		if (!parse_GLR(ex)) {
			cout << endl;
			cout << "error parsing expression: " << *ex << endl;
			cout << "expression no.: " << c++ << endl;
			ret = false;
			throw Error("expression syntax error");
			//parse(ex, true);
			//cout << err.what() << endl;
			//throw err;
		}
	}
	t.stop();
	cout << "done in " << t << endl;
	return ret;
}

bool parse_LL() {
	Timer t;
	t.start();
	cout << "parsing with LL ... " << flush;
	bool ret = true;
	for (Expr* ex : queue) {
		if (!parse_LL(ex)) {
			cout << "failed. ";
			ret = false;
			break;
		}
	}
	t.stop();
	cout << "done in " << t << endl;
	return ret;
}

} // anonymous namespace

void enqueue(Expr& ex) {
	queue.push_back(&ex);
}

bool parse() {
	if (parse_LL()) {
		queue.clear();
		return true;
	} else if (parse_LR()) {
		queue.clear();
		return true;
	} else
		return false;
}

}}} // namespace mdl::rus::expr

//#include <boost/range/adaptor/reversed.hpp>

#include <new>

#include "GLR.hpp"
#include "rus/expr/table.hpp"

namespace mdl { namespace rus { namespace expr { namespace {

typedef Expr::Node Node;
typedef Term<Node> Term;
typedef Tree<Rule*>::Node TreeNode;

struct Unit {
	State* state;
	Term*  term;
	Node*  node;
	Unit*  prev;
};

vector<Expr*> queue;

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
	if (!tab.actions.has(u.state))
		return false;
	Symbol x = current(n);
	if (x.type && !tab.vars.has(x.type))
		return false;
	Symbol s = x.type ? tab.vars[x.type] : x;
	if (!tab.actions[u.state].has(s))
		return false;
	for (Action act : tab.actions[u.state][s].s) {
		switch (act.kind) {
		case Action::SHIFT:
			if (!n)
				break;
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
			if (!tab.gotos.has(w.state))
				break;
			if (!tab.gotos[w.state].has(act.val.prod->left))
				break;
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

inline Rule* find_super(Type* type, Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second;
	else
		return nullptr;
}

Term* parse_LL(Node* x, Type* type, bool trace, bool initial = false) {
	if (!initial && type->rules.root) {
		vector<Term*> children;
		Node* f = x;

		stack<TreeNode*> n;
		stack<Node*> m;
		stack<TreeNode*> childnodes;
		n.push(type->rules.root);
		m.push(x);

		while (!n.empty() && !m.empty()) {
			if (Type* tp = n.top()->symb.type) {
				if (Term* child = parse_LL(m.top(), tp, trace, n.top() == type->rules.root)) {
					children.push_back(child);
					childnodes.push(n.top());
					if (!n.top()->next) {
						Term* t = new Term(f, child->last, n.top()->data, children);
						if (trace) cout << "CHILD: " << show_ast(t, true) << endl;
						return t;
					} else if (!child->last->next)
						goto end;
					else {
						n.push(n.top()->next);
						m.push(child->last->next);
					}
					continue;
				}
			} else if (n.top()->symb == m.top()->symb) {
				if (!n.top()->next) {
					Term* t = new Term(f, m.top(), n.top()->data, children);
					if (trace) cout << "END: " << show_ast(t, true) << endl;
					return t;
				} else if (!m.top()->next)
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
				if (!childnodes.empty() && childnodes.top() == n.top()) {
					children.pop_back();
					childnodes.pop();
				}
				if (n.empty() || m.empty()) goto end;
			}
			n.top() = n.top()->side;
		}
		end:
		for (auto t : children) delete t;
	}
	if (x->symb.type) {
		if (x->symb.type == type) {
			Term* t = new Term(x);
			if (trace) cout << "VAR: " << show_ast(t, true) << endl;
			return t;
		} else if (Rule* super = find_super(x->symb.type, type)) {
			Term* t = new Term(x, super);
			if (trace) cout << "SUPER: " << show_ast(t, true) << endl;
			return t;
		}
	}
	return nullptr;
}


/*
Term* parse_LL(Node* x, Type* type) {
	if (x->symb.type){
		if (x->symb.type == type)
			return new Term(x);
		else if (Rule* super = find_super(x->symb.type, type))
			return new Term(x, super);
	}
	if (!type->rules.root) return nullptr;
	vector<Term*> children;
	Node* f = x;

	stack<TreeNode*> n;
	stack<Node*> m;
	stack<TreeNode*> childnodes;
	n.push(type->rules.root);
	m.push(x);

	while (!n.empty() && !m.empty()) {
		if (Type* tp = n.top()->symb.type) {
			if (Term* child = parse_LL(m.top(), tp)) {
				children.push_back(child);
				childnodes.push(n.top());
				if (!n.top()->next)
					return new Term(f, child->last, n.top()->data, children);
				else if (!child->last->next)
					goto end;
				else {
					n.push(n.top()->next);
					m.push(child->last->next);
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
			if (!childnodes.empty() && childnodes.top() == n.top()) {
				children.pop_back();
				childnodes.pop();
			}
			if (n.empty() || m.empty()) goto end;
		}
		n.top() = n.top()->side;
	}
	end:
	for (auto t : children) delete t;
	return nullptr;
}

 */

bool parse_LR() {
	Timer t;
	t.start();
	cout << "creating LR parsing tables ... " << endl;
	cout << table().show();
	t.stop();
	cout << "done in " << t << endl;
	//cout << show_grammar() << endl;
	bool ret = true;
	t.start();
	cout << "parsing with LR ... " << flush;
	for (Expr* ex : queue) {
		if (!expr::parse_GLR(ex)) {
			ret = false;
			break;
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
	//cout << endl;
	//int c = 0;
	for (Expr* ex : queue) {
		//cout << "doing " << c++ << ", free: " << get_current_free() << " , exp: " << show(*ex) << " ... " << flush;
		try {
			if (!expr::parse_LL(ex)) {
				ret = false;
				break;
			}
		} catch (std::bad_alloc& ba) {
			std::cerr << "bad_alloc caught: " << ba.what() << '\n';
		}
		//cout << "done" << endl;
	}
	t.stop();
	cout << "done in " << t << endl;
	return ret;
}

} // anonymous namespace

bool parse_GLR(Expr* ex) {
	Node* n = ex->first;
	Table& tab = table();
	if (!tab.inits.has(ex->type))
		return false;
	State* init = tab.inits[ex->type];
	return parse_GLR(tab, ex, n, Unit{init, nullptr, n, nullptr});
}

bool parse_LL(Expr* ex, bool trace) {
	if (Term* term = parse_LL(ex->first, ex->type, trace)) {
		add_terms(term);
		return true;
	} else
		return false;
}


void enqueue(Expr& ex) {
	if (!parse_LL(&ex)) {
		throw Error("expression parsing error", show(ex));
	}
	//queue.push_back(&ex);
}

bool parse() {
	return true;
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

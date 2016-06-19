//#include <boost/range/adaptor/reversed.hpp>

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

bool parse_GLR(Expr* ex, bool trace = false) {
	Node* n = ex->first;
	Table& tab = table();
	if (!tab.inits.has(ex->type))
		return false;
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

Term* parse_LL(Node* x, Type* type, bool trace) {
	if (x->symb.type){
		if (x->symb.type == type)
			return new Term(x);
		else if (Rule* super = find_super(x->symb.type, type))
			return new Term(x, super);
	}
	if (!type->rules.root) return nullptr;
	vector<Term*> children;
	vector<TreeNode*> childnodes;
	Node* f = x;

	vector<TreeNode*> n;
	vector<Node*> m;
	n.push_back(type->rules.root);
	m.push_back(x);

	while (!n.empty() && !m.empty()) {
		if (Type* tp = n.back()->symb.type) {
			if (Term* child = parse_LL(m.back(), tp, trace)) {
				children.push_back(child);
				childnodes.push_back(n.back());
				if (!n.back()->next)
					return new Term(f, child->last, n.back()->data, children);
				else if (!child->last->next)
					goto end;
				else {
					n.push_back(n.back()->next);
					m.push_back(child->last->next);
				}
				continue;
			}
		} else if (n.back()->symb == m.back()->symb) {
			if (!n.back()->next)
				return new Term(f, m.back(), n.back()->data, children);
			else if (!m.back()->next)
				goto end;
			else {
				n.push_back(n.back()->next);
				m.push_back(m.back()->next);
			}
			continue;
		}
		while (!n.back()->side) {
			n.pop_back();
			m.pop_back();
			if (!childnodes.empty() && childnodes.back() == n.back()) {
				children.pop_back();
				childnodes.pop_back();
			}
			if (n.empty() || m.empty()) goto end;
		}
		n.back() = n.back()->side;
	}
	end:
	for (auto t : children) delete t;
	return nullptr;
}


bool parse_LL(Expr* ex, bool trace = false){
	if (Term* term = parse_LL(ex->first, ex->type, trace)) {
		add_terms(term);
		return true;
	} else
		return false;
}


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
		if (!parse_GLR(ex)) {
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
	for (Expr* ex : queue) {
		if (!parse_LL(ex)) {
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

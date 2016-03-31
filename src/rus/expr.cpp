#include "rus/globals.hpp"

namespace mdl {
namespace rus {

string show(Symbol s) {
	return show_sy(s.lit);
}

Symbol::Symbol(string s) : lit(-1), rep(false), type(nullptr) {
	lit = Rus::mod().lex.symbs.toInt(s);
}

string show(const Expr& ex) {
	string s;
	Expr::Node* n = ex.first;
	while (n) {
		s += show(n->symb) + " ";
		n = n->next;
	}
	return s;
}

string show_ast(const ExprTerm* t) {
	if (t->isvar()) {
		return show(t->first->symb) + " ";
	} else {
		string s = (t->rule ? show_id(t->rule->id) : "?") + " (";
		for (uint i = 0; i < t->children.size(); ++ i) {
			s += show_ast(t->children[i]);
			if (i + 1 < t->children.size()) s += ", ";
		}
		s += ")";
		return s;
	}
}

Expr::Expr(const mdl::Expr& ex) : first(nullptr), last(nullptr), type(nullptr) {
	for (auto it = ex.symbols.begin(); it != ex.symbols.end(); ++ it) {
		// pass the first symbol
		if (it == ex.symbols.begin())
			continue;
		push_back(*it);
	}
}

void Expr::push_back(Symbol s) {
	if (!first) {
		first = new Node(s);
		last  = first;
	} else {
		last->next = new Node(s);
		last->next->prev = last;
		last = last->next;
	}
}

void Expr::push_front(Symbol s) {
	if (!first) {
		first = new Node(s);
		last  = first;
	} else {
		first->prev = new Node(s);
		first->prev->next = first;
		first = first->prev;
	}
}

bool Expr::operator == (const Expr& ex) const {
	const Node* n = ex.first;
	const Node* m = first;
	while (n && m) {
		if (n->symb != m->symb) return false;
		n = n->next; m = m ->next;
	}
	return !n && !m;
}

inline Type* find_type(Vars& vars, Symbol s) {
	for (auto var : vars.v)
		if (var.lit == s.lit) return var.type;
	return nullptr;
}

inline Type* find_type(vector<Vars>& var_stack, Symbol s) {
	for (auto& vars : var_stack)
		if (Type* tp = find_type(vars, s)) return tp;
	return nullptr;
}

void mark_vars(Expr& ex, vector<Vars>& var_stack) {
	Expr::Node* n = ex.first;
	while (n) {
		n->symb.type = find_type(var_stack, n->symb);
		bool is_var = n->symb.type != nullptr;
		bool is_const = Rus::get().math.consts.has(n->symb);
		if (is_const && is_var)
			throw Error("constant symbol is marked as variable");
		if (!is_const && !is_var)
			throw Error("symbol neither constant nor variable");
		n = n->next;
	}
}

inline Rule* find_super(Type* type, Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second;
	else
		return nullptr;
}


void assemble_expr(Expr& ex, const ExprTerm* t) {
	if (!t->rule) {
		ex.push_back(t->first->symb);
		ExprTerm* at = new ExprTerm(ex.first);
		ex.first->init.push_back(at);
		ex.last->final.push_back(at);
		return;
	}
	uint i = 0;
	Expr::Node* n = t->rule->term.first;
	while (n) {
		if (n->symb.type)
			assemble_expr(ex, t->children[i++]);
		else
			ex.push_back(n->symb);
		n = n->next;
	}
	ExprTerm* at = new ExprTerm(ex.first, ex.last, t->rule);
	ex.first->init.push_back(at);
	ex.last->final.push_back(at);
}

Expr assemble(const Expr& ex) {
	Expr e;
	assemble_expr(e, ex.term());
	e.type = ex.type;
	return e;
}



























template<typename N>
uint ind_in_expr(const N* n) {
	uint ind = 0;
	while (n->prev) {
		++ ind;
		n = n->prev;
	}
	return ind;
}
template<typename N>
string show_w_ind(const Term<N>& t) {
	deque<Symbol> symbs;
	deque<uint> inds;
	for (auto it = t.rbegin(); it != t.rend(); -- it) {
		symbs.push_front(it->symb);
		inds.push_front(ind_in_expr(&*it));
	}
	string str;
	uint i = 0;
	for (auto s : symbs)
		str += show(s) + "["+to_string(inds[i++]) + "] ";
	return str;
}
string show_w_ind(const Expr& ex) {
	string str;
	uint i = 0;
	Expr::Node* n = ex.first;
	while (n) {
		str += show(n->symb) + "[" + to_string(i++) + "] ";
		n = n->next;
	}
	return str;
}

bool trace = false;

struct Stacks {
	Stacks() :
		pool(new set<ExprTerm*>()), n_stack(), t_stack(), depth(0) {
	}
	Stacks(const Stacks& s) :
		pool(s.pool), n_stack(s.n_stack), t_stack(s.t_stack), depth(s.depth) {
	}

	set<ExprTerm*>*            pool;
	vector<Tree<Rule*>::Node*> n_stack;
	vector<ExprTerm*>          t_stack;
	uint depth;

	void verify() const {
		if (n_stack.size() != depth || t_stack.size() != depth + 1)
			show();
		assert(n_stack.size() == depth);
		assert(t_stack.size() == depth + 1);
	}

	void push(Expr::Node* m, Tree<Rule*>::Node* n) {
		++ depth;
		n_stack.push_back(n);
		t_stack.push_back(new Term<Expr::Node>(m));
		pool->insert(t_stack.back());
	}
	ExprTerm* get_ret() {
		assert(t_stack.size() == 1);
		return t_stack.back();
	}

	void push_child(ExprTerm* ch) {
		pool->insert(ch);
		t_stack.back()->children.push_back(ch);
	}
	void pop_child() {
		assert(t_stack.back()->children.size());
		//t_stack.back()->children.back()->destroy();
		//delete t_stack.back()->children.back();
		t_stack.back()->children.pop_back();
	}

	Tree<Rule*>::Node* pop_term(Expr::Node* m, Tree<Rule*>::Node* n) {
		while (!n->next) {
			ExprTerm* ch = t_stack.back();
			ch->last = m;
			ch->rule = n->data;
			verify();
			if (n_stack.empty()) return nullptr;
			n = n_stack.back();
			pop();
			push_child(ch);
		}
		verify();
		return n;
	}

	void pop(bool del = false) {
		verify();
		assert(depth);
		-- depth;
		/*if (del) {
			t_stack.back()->destroy();
			delete t_stack.back();
		}*/
		t_stack.pop_back();
		n_stack.pop_back();
		verify();
	}

	string show() const {
		string s = "";
		s += "stack n: " + to_string(n_stack.size()) + "\n";
		for (auto ns : n_stack) {
			s += "\t" + show_backward(ns) + "\n";
		}
		s += "stack t: " + to_string(t_stack.size()) + "\n";
		for (auto ts : t_stack) {
			s += "\t" + show_ast(ts) + " = " + show_w_ind(*ts) + "\n";
		}
		return s;
	}
};

ExprTerm* parse_variants(Expr::Node* m, Tree<Rule*>::Node* n, Stacks& s);

ExprTerm* parse_next(Expr::Node* m, Tree<Rule*>::Node* n, Stacks s) {
	if (trace) {
		cout << "Nodes:" << endl;
		cout << "------" << endl;
		cout << "m:\t" << m->symb << "[" << to_string(ind_in_expr(m)) << "]" << endl;
		cout << "n:\t" << n->symb << "[" << to_string(ind_in_expr(n)) << "]" << endl;
		s.show();
	}
	if (n->next) {
		return (m->next) ? parse_variants(m->next, n->next, s) : nullptr;
	}
	n = s.pop_term(m, n);
	if (m->next) {
		if (ExprTerm* t = parse_variants(m->next, n->next, s)) return t;
		else s.pop_child();
		return nullptr;
	}
	return s.get_ret();
}


ExprTerm* parse_var(Expr::Node* m, Tree<Rule*>::Node* n, Stacks& s) {
	if (m->symb.type == n->symb.type) {
		s.push_child(new ExprTerm(m));
		if (ExprTerm* t = parse_next(m, n, s)) return t;
		else s.pop_child();
	}
	if (Rule* super = find_super(m->symb.type, n->symb.type)) {
		ExprTerm* st = new Term<Expr::Node>(m, super);
		ExprTerm* vt = new Term<Expr::Node>(m);
		st->children.push_back(vt);
		s.pool->insert(vt);
		s.push_child(st);
		if (ExprTerm* t = parse_next(m, n, s)) return t;
		else s.pop_child();
	}
	return nullptr;
}

ExprTerm* parse_variants(Expr::Node* m, Tree<Rule*>::Node* n, Stacks& s) {
	while (n) {
		if (!n->symb.type && n->symb.lit == m->symb.lit) {
			if (ExprTerm* t = parse_next(m, n, s)) return t;
		}
		if (n->symb.type) {
			if (m->symb.type) {
				if (ExprTerm* t = parse_var(m, n, s)) return t;
			}
			if (n->symb.type->rules.root) {
				s.push(m, n);
				ExprTerm* t =
					(m->symb.type == n->symb.type) ?
					parse_next(m, n->symb.type->rules.root, s) :
					parse_variants(m, n->symb.type->rules.root, s);
				if (t) return t;
				else s.pop(true);
			}
		}
		n = n->side;
	}
	return nullptr;
}


void remove_children(set<ExprTerm*>* pool, ExprTerm* t) {
	pool->erase(t);
	for (auto ch : t->children) {
		remove_children(pool, ch);
	}
}

ExprTerm* parse_term(Expr::Node* m, Type* type) {
	if (m->symb.type && !m->next) {
		if (m->symb.type == type) return new Term<Expr::Node>(m);
		else if (Rule* super = find_super(m->symb.type, type)) {
			ExprTerm* st = new Term<Expr::Node>(m, super);
			ExprTerm* vt = new Term<Expr::Node>(m);
			st->children.push_back(vt);
			return st;
		}
	}
	Stacks s;
	s.t_stack.push_back(new Term<Expr::Node>(m));
	ExprTerm* t = parse_variants(m, type->rules.root, s);
	remove_children(s.pool, t);
	static uint c = 0;
	c ++;
	if (s.pool->size() > 1000) {
		//cout << "parsing: " << c++ << " = " << show(*t) << " -- ";
		cout << c << ": extra terms: " << s.pool->size() << show(*t) << endl;
	}
	for (auto x : *s.pool) delete x;
	delete s.pool;
	return t;
}




void add_terms(Term<node::Expr>* term) {
	for (auto t : term->children) add_terms(t);
	term->first->init.push_back(term);
	term->last->final.push_back(term);
}

void parse_expr(Expr& ex, vector<Vars>& var_stack){
	mark_vars(ex, var_stack);
	if (Term<node::Expr>* term = parse_term(ex.first, ex.type)) {
		//Expr e;
		//assemble_expr(term, e);
		//assert(e == ex);
		add_terms(term);
	} else {
		trace = true;
		cout << "parsing: " << show(ex) << endl;
		cout << "parsing: " << show_w_ind(ex) << endl;
		parse_term(ex.first, ex.type);
		throw Error("could not parse the expression", show(ex));
	}
}

Term<node::Expr>* create_term(Expr::Node* first, Expr::Node* last, Rule* rule) {
	Term<node::Expr>* term = new Term<node::Expr>(first, last, rule);
	Expr::Node* n = first;
	while (n) {
		if (n->symb.type)
			term->children.push_back(new Term<node::Expr>(n));
		n = n->next;
	}
	return term;
}

void parse_term(Expr& ex, vector<Vars>& var_stack, Rule* rule) {
	mark_vars(ex, var_stack);
	add_terms(create_term(ex.first, ex.last, rule));
}

template<typename N>
inline Type* type(const Term<N>* t) {
	return t->rule ? t->rule->type : t->first->symb.type;
}

Sub<>* unify(const Term<Expr::Node>* p, const Term<Expr::Node>* q) {
	if (p->isvar()) {
		Symbol var = p->first->symb;
		if (var.type == type(q)) {
			Sub<>* s = new Sub<>();
			s->sub[var] = q->clone();
			return s;
		} else if (Rule* super = find_super(const_cast<Type*>(var.type), type(q))) {
			Sub<>* s = new Sub<>();
			s->sub[var] = new Term<Expr::Node>(q->first, q->last, super);
			s->sub[var]->children.push_back(q->clone());
			return s;
		}
		return nullptr;
	} else {
		if (p->rule != q->rule) {
			return nullptr;
		}
		Sub<>* sub = new Sub<>();
		auto p_ch = p->children.begin();
		auto q_ch = q->children.begin();
		while (p_ch != p->children.end()) {
			if (Sub<>* s = unify(*p_ch, *q_ch)) {
				if (!sub->join(s)) {
					delete sub;
					return nullptr;
				}
				delete s;
			} else {
				delete sub;
				return nullptr;
			}
			++p_ch;
			++q_ch;
		}
		return sub;
	}
}


void dump(const Symbol& s) { cout << show(s) << endl; }
void dump(const Expr& ex) { cout << show(ex) << endl; }
void dump_ast(const Expr& ex) { cout << show_ast(ex) << endl; }
void dump(const Term<Expr::Node>* tm) { cout << show(*tm) << endl; }
void dump_ast(const Term<Expr::Node>* tm) { cout << show_ast(tm) << endl; }
void dump(const Sub<Expr::Node>& sb) { cout << show(sb) << endl; }

}} // mdl::rus

#include "rus/globals.hpp"

namespace mdl {
namespace rus {

string show(Symbol s) {
	return show_sy(s.lit);
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

string show_ast(const Term<Expr::Node>* t) {
	if (t->isvar()) {
		return show(t->first->symb) + " ";
	} else {
		string s = show_id(t->rule->id) + "(";
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

bool trace = false;

inline Rule* find_super(Type* type, Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second;
	else
		return nullptr;
}

Term<node::Expr>* parse_term(Expr::Node* x, Type* type) {
	if (x->symb.type){
		if (x->symb.type == type)
			return new Term<node::Expr>(x);
		else if (Rule* super = find_super(x->symb.type, type))
			return new Term<node::Expr>(x, super);
	}
	if (!type->rules.root) return nullptr;
	vector<Term<node::Expr>*> children;
	Expr::Node* f = x;

	stack<Tree<Rule*>::Node*> n;
	stack<Expr::Node*> m;
	n.push(type->rules.root);
	m.push(x);

	while (!n.empty() && !m.empty()) {
		if (Type* tp = n.top()->symb.type) {
			if (Term<node::Expr>* child = parse_term(m.top(), tp)) {
				children.push_back(child);
				m.top() = child->last;
				if (!n.top()->next)
					return new Term<node::Expr>(f, m.top(), n.top()->data, children);
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
				return new Term<node::Expr>(f, m.top(), n.top()->data, children);
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

void add_terms(Term<node::Expr>* term) {
	for (auto t : term->children) add_terms(t);
	term->first->init.push_back(term);
	term->last->final.push_back(term);
}

void parse_expr(Expr& ex, vector<Vars>& var_stack){
	mark_vars(ex, var_stack);
	if (Term<node::Expr>* term = parse_term(ex.first, ex.type))
		add_terms(term);
	else {
		trace = true;
		parse_term(ex.first, ex.type);
		throw Error("error at parsing", show(ex));
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

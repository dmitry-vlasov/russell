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


template<typename N>
inline bool shift_next(N*& n) {
	if (n->next) { n = n->next; return true; } else return false;
}

template<typename N>
inline bool shift_side(N*& n) {
	if (n->side) { n = n->side; return true; } else return false;
}

Term<node::Expr>* parse_term(Expr::Node* last, Type* type) {
	if (last->symb.type){
		if (last->symb.type == type) {
			return new Term<node::Expr>(last, last, nullptr);
		} else if (Rule* super = type->supers.find(last->symb.type)->second) {
			return new Term<node::Expr>(last, last, super);
		}
	}
	Tree<Rule*>::Node* n = type->rules.root;
	vector<Term<node::Expr>*> children;
	Expr::Node* first = last;
	while (n && last) {
		if (Type* tp = n->symb.type) {
			if (Term<node::Expr>* child = parse_term(last, tp)) {
				children.push_back(child);
				if (!shift_next(n)) break;
				last = child->last->next;
				continue;
			}
		} else if (n->symb == last->symb) {
			if (!shift_next(n)) break;
			last = last->next;
			continue;
		}
		if (!shift_side(n)) break;
	}
	if (last && !n->next) {
		Term<node::Expr>* term = new Term<node::Expr>(first, last, n->data);
		term->children = children;
		return term;
	} else {
		for (auto t : children) delete t;
		return nullptr;
	}
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
	else
		throw Error("error at parsing", show(ex));
}

void parse_term(Expr& ex, vector<Vars>& var_stack, Rule* rule){
	mark_vars(ex, var_stack);
	add_terms(new Term<node::Expr>(ex.first, ex.last, rule));
}

template<typename N>
inline Type* type(Term<N>* t) {
	return t->rule ? t->rule->type : t->first->symb.type;
}

Sub<>* try_unify(Term<Expr::Node>* p, Term<Expr::Node>* q) {
	if (p->isvar()) {
		Symbol var = p->first->symb;
		if (var.type == type(q)) {
			Sub<>* s = new Sub<>();
			s->sub[var] = q->clone();
			return s;
		} else if (Rule* super = type(q)->supers.find(var.type)->second) {
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
			if (Sub<>* s = try_unify(*p_ch, *q_ch)) {
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

Sub<>* Expr::unify(Expr& ex) {
	return try_unify(term(), ex.term());
}


}} // mdl::rus

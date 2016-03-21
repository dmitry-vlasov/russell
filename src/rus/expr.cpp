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

inline bool is_suptype(Type* sup, Type* inf) {
	return (sup == inf) || (std::find(inf->sup.begin(), inf->sup.end(), sup) != inf->sup.end());
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
	Tree<Rule*>::Node* n = type->rules.root;
	vector<Term<node::Expr>*> children;
	Expr::Node* first = last;
	while (n && last) {
		if (Type* tp = n->symb.type) {
			if (is_suptype(tp, last->symb.type)) {
				if (!shift_next(n)) break;
				last = last->next;
				continue;
			} else if (Term<node::Expr>* child = parse_term(last, tp)) {
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
	if (!n->next) {
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
	//Term<node::Expr>* term = parse_term(ex.first, ex.type);
	//add_terms(term);
}

void parse_term(Expr& ex, vector<Vars>& var_stack, Rule* rule){
	mark_vars(ex, var_stack);
	Term<node::Expr>* term = new Term<node::Expr>(ex.first, ex.last, rule);
	add_terms(term);
}


}} // mdl::rus

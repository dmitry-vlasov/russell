#include "rus/globals.hpp"

namespace mdl {
namespace rus {

string show(Symbol s, bool full) {
	if (!full || !s.type)
		return show_sy(s.lit);
	else {
		return string("<") + show_sy(s.lit) + ":" + show_id(s.type->id) + ">";
	}
}

Symbol::Symbol(string s, Type* t) : lit(-1), rep(false), type(t) {
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

size_t memvol(const Expr& ex) {
	size_t s = 0;
	Expr::Node* n = ex.first;
	while (n) {
		s += memsize(*n);
		for (Term<Expr::Node>* t : n->init)
			s += memsize(*t);
		n = n->next;
	}
	return s;
}

string show_ast(const ExprTerm* t, bool full) {
	if (t->isvar())
		return show(t->first->symb, full);
	else {
		string s = (t->rule ? show_id(t->rule->id) : "?") + " (";
		for (uint i = 0; i < t->children.size(); ++ i) {
			s += show_ast(t->children[i], full);
			if (i + 1 < t->children.size()) s += ", ";
		}
		s += ")";
		return s;
	}
}

Expr::Expr(const Expr& ex) : first(nullptr), last(nullptr), type(ex.type) {
	map<Node*, Node*> mp;
	Node* n = ex.first;
	while (n){
		push_back(n->symb);
		mp[n] = last;
		n = n->next;
	}
	add_term(ex.term(), mp);
}
Expr::Expr(Expr&& ex) : first(ex.first), last(ex.last), type(ex.type) {
	ex.first = nullptr;
	ex.last  = nullptr;
	ex.type  = nullptr;
}
Expr::~Expr() {
	Node* n = last;
	while (n) {
		Node* to_delete = n;
		n = n->prev;
		delete to_delete;
	}
}
Expr& Expr::operator = (const Expr& ex) {
	Node* n = last;
	while (n) {
		Node* to_delete = n;
		n = n->prev;
		delete to_delete;
	}
	last = nullptr;
	first = nullptr;
	type = ex.type;
	map<Node*, Node*> mp;
	n = ex.first;
	while (n){
		push_back(n->symb);
		mp[n] = last;
		n = n->next;
	}
	add_term(ex.term(), mp);
	return *this;
}
Expr& Expr::operator = (Expr&& ex) {
	first = ex.first;
	last  = ex.last;
	type  = ex.type;
	ex.first = nullptr;
	ex.last  = nullptr;
	ex.type  = nullptr;
	return *this;
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

Symbol Expr::pop_back() {
	assert(first);
	assert(last->final.empty());
	assert(last->init.empty());
	Symbol s = last->symb;
	if (last == first) {
		delete first;
		first = nullptr;
	} else {
		last = last->prev;
		delete last->next;
	}
	return s;
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


inline Rule* find_super(Type* type, Type* super) {
	auto it =type->supers.find(super);
	if (it != type->supers.end())
		return it->second;
	else
		return nullptr;
}

ExprTerm* assemble_expr(Expr& ex, const ExprTerm* t) {
	if (t->isvar()) {
		ex.push_back(t->first->symb);
		ExprTerm* at = new ExprTerm(ex.first);
		ex.first->init.push_back(at);
		ex.last->final.push_back(at);
		return at;
	}
	uint i = 0;
	Expr::Node* n = t->rule ? t->rule->term.first : t->first;
	vector<ExprTerm*> children;
	while (n) {
		if (n->symb.type) {
			if (i + 1 > t->children.size()) {
				cout << " ERROR!!" << endl;
				ex.push_back(Symbol("<<"));
				ex.push_back(n->symb);
				ex.push_back(Symbol(">>"));
			} else {
				ExprTerm* ch = assemble_expr(ex, t->children[i++]);
				children.push_back(ch);
			}
		} else
			ex.push_back(n->symb);
		n = n->next;
	}
	ExprTerm* at = new ExprTerm(ex.first, ex.last, t->rule, children);
	ex.first->init.push_back(at);
	ex.last->final.push_back(at);
	return at;
}

Expr assemble(const ExprTerm* t) {
	Expr e;
	assemble_expr(e, t);
	e.type = t->rule ? t->rule->type : t->first->symb.type;
	return e;
}

Expr assemble(const Expr& ex) {
	return assemble(ex.term());
}

void add_terms(Term<node::Expr>* term) {
	for (auto t : term->children) add_terms(t);
	term->first->init.push_back(term);
	term->last->final.push_back(term);
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

void parse_term(Expr& ex, Rule* rule) {
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
		} else if (Rule* super = find_super(type(q), const_cast<Type*>(var.type))) {
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

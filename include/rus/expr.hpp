#pragma once

#include "common.hpp"

namespace mdl { namespace rus {

struct Type;

struct Symbol {
	Symbol(string s, Type* t = nullptr);
	Symbol(): lit(-1), rep(false), type(nullptr) { }
	Symbol(uint l): lit(l), rep(false), type(nullptr) { }
	Symbol(const mdl::Symbol s, bool r = false) :
	lit(s.lit), rep(r), type(nullptr) {
	}
	Symbol(const mdl::Symbol s, Type* tp, bool r = false) :
	lit(s.lit), rep(r), type(tp) {
	}
	bool operator == (const Symbol& s) const {
		return lit == s.lit && type == s.type;
	}
	bool operator != (const Symbol& s) const {
		return !operator ==(s);
	}
	bool operator < (const Symbol& s) const {
		return type == s.type ? lit < s.lit : type < s.type;
	}
	bool undef() const { return lit == (uint)-1; }
	uint  lit;
	bool  rep;
	Type* type;
};

string show(Symbol s, bool full = false);

inline ostream& operator << (ostream& os, Symbol s) {
	os << show(s);
	return os;
}

template<typename N>
struct iterator {
	typedef N Node;
	iterator() : n(nullptr) { }
	iterator(Node* nd) : n(nd) { }
	iterator& operator ++() { n = n->next; return *this; }
	iterator& operator +()  { n = n->side; return *this; }
	iterator& operator --() { n = n->prev; return *this; }
	bool operator == (iterator it) { return n == it.n; }
	bool operator != (iterator it) { return !operator == (it); }
	Node& operator *()   { return *n; }
	Node* operator -> () { return n; }
	iterator next() const { return n->next; }
	iterator side() const { return n->side; }
	N* n;
};

template<typename N>
struct const_iterator {
	typedef N Node;
	const_iterator() : n(nullptr) { }
	const_iterator(const Node* nd) : n(nd) { }
	const_iterator& operator ++() { n = n->next; return *this; }
	const_iterator& operator +()  { n = n->side; return *this; }
	const_iterator& operator --() { n = n->prev; return *this; }
	bool operator == (const_iterator it) { return n == it.n; }
	bool operator != (const_iterator it) { return !operator == (it); }
	const Node& operator *()   { return *n; }
	const Node* operator -> () { return n; }
	const_iterator next() const { return n->next; }
	const_iterator side() const { return n->side; }
	const N* n;
};

// Iterator modificators

template<typename I>
class memorized : I {
	memorized() : I() { }
	memorized(I i) : I(i), mem() { }
	void remember() { mem = *this; }
	void recall() { *this = mem; }
	I mem;
};

template<typename I>
struct tracing : I {
	tracing() : I(), back() { }
	tracing(I i) : I(i), back() { }
	void unshift() { *this = back; }
	tracing& operator ++() { back = *this; I::operator ++(); return *this; }
	tracing& operator +()  { back = *this; I::operator  +(); return *this; }
	tracing& operator --() { back = *this; I::operator --(); return *this; }
	I back;
};

template<typename I>
struct identical : I {
	identical() : I() { }
	identical(I i) : I(i) { }
};

template<typename I>
struct treeing : I {
	treeing() : I() { }
	treeing(I i) : I(i) { }
	treeing& operator +()  { I::n = nullptr; return *this; }
};

template<typename I1, typename I2, template<typename> class Wrapper = identical>
struct pairing {
	typedef pairing<I2, I1> reversed;
	pairing() : first(), second() { }
	pairing(I1 i1, I2 i2) : first(i1), second(i2) { }
	pairing& operator ++() { ++first; ++second; return *this; }
	pairing& operator +()  { +first;  +second;  return *this; }
	pairing& operator --() { --first; --second; return *this; }
	reversed reverse() { return reversed(second, first); }
	bool equal() const { return first.n->symb == second.n->symb; }
	bool defined() const { return first.n && second.n; }
	pairing next() const { return pairing(first.next(), second.next()); }
	pairing side() const { return pairing(first.side(), second.side()); }
	Wrapper<I1> first;
	Wrapper<I2> second;
};

struct Rule;

template<typename N>
struct Term {
	typedef N Node;
	typedef iterator<Node> Iterator;
	typedef const_iterator<Node> ConstIterator;

	Term(Node* f, Node* l, Rule* r) :
	first(f), last(l), rule(r), children() { }
	Term(Node* v, Rule* r = nullptr) :
	first(v), last(v), rule(r), children() { }
	Term(Node* f, Node* l, Rule* r, const vector<Term*>& ch) :
	first(f), last(l), rule(r), children(ch) { }

	Iterator begin() { return Iterator(first); }
	Iterator end()   { return last->next ? Iterator(last->next) : Iterator(); }
	ConstIterator begin() const { return ConstIterator(first); }
	ConstIterator end() const { return last->next ? ConstIterator(last->next) : ConstIterator(); }
	Iterator rbegin() { return Iterator(last); }
	Iterator rend() { return first->prev ? Iterator(first->prev) : Iterator(); }
	ConstIterator rbegin() const { return ConstIterator(last); }
	ConstIterator rend() const { return first->prev ? ConstIterator(first->prev) : ConstIterator(); }

	bool isvar() const { return first == last && first->symb.type; }
	Symbol getvar() const { return first->symb; }

	Term* clone() const;
	bool operator == (const Term& t) const;
	bool operator != (const Term& t) const {
		return !operator == (t);
	}
	void destroy() {
		for(auto ch : children) {
			ch->destroy();
			delete ch;
		}
	}

	Node* first;
	Node* last;
	Rule* rule;
	vector<Term*> children;
};

namespace node {

struct Expr {
	Expr() : symb(), next(nullptr),
	prev(nullptr), init(), final() { }
	Expr(Symbol s) : symb(s), next(nullptr),
	prev(nullptr), init(), final() { }
	~Expr() {
		for (auto t : init) delete t;
	}
	Expr(const Expr& ex) : symb(ex.symb), next(nullptr),
	prev(nullptr), init(), final() {
	}
	Expr& operator = (const Expr& ex) {
		symb = ex.symb;
		next = nullptr;
		prev = nullptr;
		init.clear();
		final.clear();
		return *this;
	}
	Symbol symb;
	Expr*  next;
	Expr*  prev;
	vector<Term<Expr>*>  init;
	vector<Term<Expr>*> final;
};

template<typename T>
struct Tree {
	Tree() : symb(), next(nullptr),
	prev(nullptr), side(nullptr), init(), final(), data() { }
	Tree(Symbol s) : symb(s), next(nullptr),
	prev(nullptr), side(nullptr), init(), final(), data() { }
	~Tree() {
		for (auto t : init) delete t;
	}
	Tree(const Tree& tr) : symb(tr.symb), next(nullptr),
	prev(nullptr), side(nullptr), init(), final(), data() {
	}
	Tree& operator = (const Tree& tr) {
		symb = tr.symb;
		next = nullptr;
		prev = nullptr;
		side = nullptr;
		init.clear();
		final.clear();
		return *this;
	}
	Symbol symb;
	Tree*  next;
	Tree*  prev;
	Tree*  side;
	uint   level;
	vector<Term<Tree>*>  init;
	vector<Term<Tree>*> final;
	T data;
};

} // namespace node

struct Expr;

template<typename T>
struct Tree {
	typedef node::Tree<T> Node;
	Tree() : root(nullptr) { }
	~Tree();
	T& add(const Expr& ex);
	Node* root;
};

template<typename N = node::Expr>
struct Sub {
	typedef N Node;
	~Sub() {
		for (auto p : sub) {
			p.second->destroy();
			delete p.second;
		}
	}
	bool join(Sub* s);
	Term<Node>* find(Symbol v) {
		auto it = sub.find(v);
		if (it == sub.end()) return nullptr;
		else return it->second;
	}

	map<Symbol, Term<Node>*> sub;
};

struct Expr {
	typedef node::Expr Node;
	typedef iterator<Node> Iterator;
	typedef const_iterator<Node> ConstIterator;

	Expr() : first(nullptr), last(nullptr), type(nullptr) { }
	Expr(Symbol s) : first(nullptr), last(nullptr), type(s.type) {
		push_back(s);
	}
	Expr(const Expr&);
	Expr(Expr&&);
	~Expr();
	Expr& operator = (const Expr&);
	Expr& operator = (Expr&&);
	void copy(const Expr&);
	void push_back(Symbol);
	void push_front(Symbol);
	Symbol pop_back();
	bool operator == (const Expr& ex) const;
	bool operator != (const Expr& ex) const {
		return !operator == (ex);
	}
	Term<Node>* term() {
		if (!first) return nullptr; else
		return first->init.size() ? first->init.back() : nullptr;
	}
	const Term<Node>* term() const {
		if (!first) return nullptr; else
		return first->init.size() ? first->init.back() : nullptr;
	}
	Iterator begin() { return Iterator(first); }
	Iterator end()   { return last->next ? Iterator(last->next) : Iterator(); }
	ConstIterator begin() const { return ConstIterator(first); }
	ConstIterator end() const { return last->next ? ConstIterator(last->next) : ConstIterator(); }
	Iterator rbegin() { return Iterator(last); }
	Iterator rend() { return first->prev ? Iterator(first->prev) : Iterator(); }
	ConstIterator rbegin() const { return ConstIterator(last); }
	ConstIterator rend() const { return first->prev ? ConstIterator(first->prev) : ConstIterator(); }

	Node* first;
	Node* last;
	Type* type;
};

typedef Term<node::Expr> ExprTerm;

inline iterator<node::Expr> begin(Expr& ex) { return ex.begin(); }
inline iterator<node::Expr> end(Expr& ex)   { return ex.end(); }
inline const_iterator<node::Expr> begin(const Expr& ex) { return ex.begin(); }
inline const_iterator<node::Expr> end(const Expr& ex) { return ex.end(); }
inline iterator<node::Expr> rbegin(Expr& ex) { return ex.rbegin(); }
inline iterator<node::Expr> rend(Expr& ex) { return ex.rend(); }
inline const_iterator<node::Expr> rbegin(const Expr& ex) { return ex.rbegin(); }
inline const_iterator<node::Expr> rend(const Expr& ex) { return ex.rend(); }


Sub<>* unify(const Term<Expr::Node>* p, const Term<Expr::Node>* q);
inline Sub<>* unify(const Expr& ex1, const Expr& ex2) {
	return unify(ex1.term(), ex2.term());
}
Expr assemble(const Expr& ex);

string show(const Expr&);
string show_ast(const Term<Expr::Node>*, bool full = false);
inline string show_ast(const Expr& ex) {
	if (ex.term())
		return show_ast(ex.term());
	else
		return "<no ast>";
}

template<typename N>
string show(const Term<N>& t) {
	deque<Symbol> symbs;
	for (auto it = t.rbegin(); it != t.rend(); -- it) {
		symbs.push_front(it->symb);
	}
	string str;
	for (auto s : symbs)
		str += show(s) + " ";
	return str;
}

template<typename N>
string show(const Sub<N>& s) {
	string str;
	for (auto p : s.sub) {
		str += show(p.first) + " --> " + show(*p.second) + "\n";
	}
	return str;
}

template<typename N>
string show_backward(const N* n) {
	deque<Symbol> symbs;
	while (n) {
		symbs.push_front(n->symb);
		n = n->prev;
	}
	string str;
	for (auto s : symbs)
		str += show(s) + " ";
	return str;
}

template<typename T>
string show_forward(const typename Tree<T>::Node* n) {
	string s;
	while (n) {
		if (!n->next)
			s += show_backward(n) + "\n";
		else
			s += show_forward<T>(n->next);
		n = n->side;
	}
	return s;
}

template<typename T>
string show(const Tree<T>& tr) {
	return show_forward<T>(tr.root);
}

inline ostream& operator << (ostream& os, const Expr& ex) {
	os << show(ex);
	return os;
}

template<typename T>
inline ostream& operator << (ostream& os, const Tree<T>& tr) {
	os << show(tr);
	return os;
}


template<typename N>
inline N* new_next(N* n, Symbol s) {
	n->next = new N(s);
	n->next->prev = n;
	return n->next;
}
template<typename N>
inline N* new_side(N* n, Symbol s) {
	n->side = new N(s);
	n->side->prev = n->prev;
	return n->side;
}

template<class N>
Term<N>* add_term(const Term<node::Expr>* st, map<Expr::Node*, N*>& mp) {
	if (!st) return nullptr;
	assert(mp.find(st->first) != mp.end());
	assert(mp.find(st->last) != mp.end());
	Term<N>* tt = new Term<N>(mp[st->first], mp[st->last], st->rule);
	mp[st->first]->init.push_back(tt);
	mp[st->last]->final.push_back(tt);
	for (auto ch : st->children) {
		tt->children.push_back(add_term(ch, mp));
	}
	return tt;
}

template<typename T>
T& Tree<T>::add(const Expr& ex) {
	assert(ex.first);
	map<Expr::Node*, Node*> mp;
	Expr::Node* m = ex.first;
	if (!root) {
		root = new Node(m->symb);
		mp[m] = root;
	}
	Node* n = root;
	while (true) {
		while (n->side && m->symb != n->symb)
			n = n->side;
		if (n->symb == m->symb && m->next && n->next) {
			mp[m] = n;
			n = n->next;
			m = m->next;
		} else break;
	}
	if (n->symb != m->symb) {
		n = new_side(n, m->symb);
		mp[m] = n;
	}
	while (m->next) {
		m = m->next;
		n = new_next(n, m->symb);
		mp[m] = n;
	}
	add_term<typename Tree<T>::Node>(ex.term(), mp);
	return n->data;
}

template<typename N>
void gather_tree_nodes(vector<N*>& nodes, N* n) {
	if (n->next)
		gather_tree_nodes(nodes, n->next);
	if (n->side)
		gather_tree_nodes(nodes, n->side);
	nodes.push_back(n);
}

template<typename T>
Tree<T>::~Tree() {
	if (root) {
		vector<Node*> nodes;
		gather_tree_nodes(nodes, root);
		root = nullptr;
		for (Node* n : nodes)
			delete n;
	}
}

template<typename N>
bool Sub<N>::join(Sub* s) {
	for (auto p : s->sub) {
		auto it = sub.find(p.first);
		if (it != sub.end()) {
			if (*(*it).second != *p.second) {
				return false;
			}
		} else {
			sub[p.first] = p.second->clone();
		}
	}
	return true;
}

template<typename N>
Term<N>* Term<N>::clone() const {
	Term* ret = new Term(first, last, rule);
	for (auto ch : children)
		ret->children.push_back(ch->clone());
	return ret;
}
template<typename N>
bool Term<N> :: operator == (const Term& t) const {
	if (isvar() && t.isvar() && first->symb == t.first->symb)
		return true;
	if (rule != t.rule)
		return false;
	auto i_p = children.begin();
	auto i_q = t.children.begin();
	while (i_p != children.end()) {
		const Term* ch_p = *i_p;
		const Term* ch_q = *i_q;
		if (*ch_p != *ch_q) return false;
		++ i_p; ++ i_q;
	}
	return true;
}

void dump(const Symbol& s);
void dump(const Expr& ex);
void dump_ast(const Expr& ex);
void dump(const Term<Expr::Node>* tm);
void dump_ast(const Term<Expr::Node>* tm);
void dump(const Sub<Expr::Node>& sb);


}} // mdl::rus

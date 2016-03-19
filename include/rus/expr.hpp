#pragma once

#include "common.hpp"

namespace mdl { namespace rus {

struct Type;

struct Symbol {
	Symbol(): lit(-1), rep(false), type(nullptr) { }
	Symbol(const mdl::Symbol s, bool r = false) :
	lit(s.lit), rep(r), type(nullptr) {
	}
	Symbol(const mdl::Symbol s, bool r, Type* tp) :
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

string show(Symbol s);

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

template<typename I1, typename I2>
struct pairing {
	typedef pairing<I2, I1> reversed;
	pairing() : first(), second() { }
	pairing(I1 i1, I2 i2) : first(i1), second(i2) { }
	pairing& operator ++() { ++first; ++second; return *this; }
	pairing& operator +()  { +first;  +second;  return *this; }
	pairing& operator --() { --first; --second; return *this; }
	reversed reverse() { return reversed(second, first); }
	I1 first;
	I2 second;
};

struct Rule;

template<typename N>
struct Term {
	typedef N Node;
	typedef iterator<Node> Iterator;
	typedef const_iterator<Node> ConstIterator;

	Iterator begin() { return Iterator(b); }
	Iterator end()   { return Iterator(); }
	ConstIterator begin() const { return ConstIterator(b); }
	ConstIterator end() const { return ConstIterator(); }
	Iterator rbegin() { return Iterator(e); }
	Iterator rend() { return Iterator(); }
	const Node* rbegin() const { return ConstIterator(e); }
	const Node* rend() const { return ConstIterator(); }

	Node* b;
	Node* e;
	Rule* rule;
	vector<Term*> children;
};

namespace node {

struct Expr {
	Expr() : symb(), next(nullptr),
	prev(nullptr), init(), final() { }
	Expr(Symbol s) : symb(s), next(nullptr),
	prev(nullptr), init(), final() { }
	Symbol symb;
	Expr*  next;
	Expr*  prev;
	vector<Term<Expr>> init;
	vector<Term<Expr>> final;
};

template<typename T>
struct Tree {
	Tree() : symb(), next(nullptr),
	prev(nullptr), side(nullptr), init(), final(), data() { }
	Tree(Symbol s) : symb(s), next(nullptr),
	prev(nullptr), side(nullptr), init(), final(), data() { }
	Symbol symb;
	Tree*  next;
	Tree*  prev;
	Tree*  side;
	uint   level;
	vector<Term<Tree>> init;
	vector<Term<Tree>> final;
	T data;
};

} // namespace node

struct Expr;

template<typename T>
struct Tree {
	typedef node::Tree<T> Node;
	typedef tracing<iterator<Node>> iter_tree;
	typedef tracing<iterator<node::Expr>> iter_expr;
	typedef pairing<iter_tree, iter_expr> iter_pair;


	bool add_common(iter_pair& i) {

	}

	Tree() : root(nullptr) { }
	void add(Expr& ex, T data) {
		/*Iter i(root);
		for (auto n : ex.term) {
			Iter last;
			bool new_node = true;
			for (Iter j = i; j != Iter(); + j) {
				if (j->symb == n.symb) {
					++ i;
					new_node = false
					break;
				}
				last = j;
			}
			last->side = new Node(n.symb);
			i = + last;
		}*/
	}
	Node* root;
};


struct Expr {
	typedef node::Expr Node;
	Expr() : term(), type(nullptr) { }
	Expr(const mdl::Expr&);
	void destroy();
	void push_back(Symbol);
	Term<Node> term;
	Type*      type;
};

string show(const Expr&);

inline ostream& operator << (ostream& os, const Expr& ex) {
	os << show(ex);
	return os;
}

template<typename N = node::Expr>
struct Sub {
	typedef N Node;
	map<Symbol, Term<Node>> sub;
};

}} // mdl::rus

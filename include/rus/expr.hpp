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
	bool operator == (const Symbol& s) const { return lit == s.lit; }
	bool operator != (const Symbol& s) const { return !operator ==(s); }
	bool operator < (const Symbol& s) const { return lit < s.lit; }
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
class iterator {
	N* n;
public :
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
};

template<typename N>
class const_iterator {
	const N* n;
public :
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

struct List {
	List() : symb(), next(nullptr),
	prev(nullptr), init(), final() { }
	List(Symbol s) : symb(s), next(nullptr),
	prev(nullptr), init(), final() { }
	Symbol symb;
	List*  next;
	List*  prev;
	vector<Term<List>> init;
	vector<Term<List>> final;
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

struct Expr {
	Expr() : term() { }
	Expr(const mdl::Expr&);
	void push_back(Symbol);
	void parse();
	Term<List> term;
	Type* type();
};

string show(const Expr&);

inline ostream& operator << (ostream& os, const Expr& ex) {
	os << show(ex);
	return os;
}

template<typename N = List>
struct Sub {
	typedef N Node;
	map<Symbol, Term<Node>> sub;
};

}} // mdl::rus

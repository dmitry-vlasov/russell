#pragma once

#include "common.hpp"

namespace mdl { namespace rus {

struct Type;

struct Symbol {
	Symbol(): lit(0), rep(false), type(nullptr) { }
	bool operator == (const Symbol& s) const { return lit == s.lit; }
	bool operator != (const Symbol& s) const { return !operator ==(s); }
	bool operator < (const Symbol& s) const { return lit < s.lit; }
	uint  lit:30;
	char  rep:1;
	char  res:1;
	Type* type;
};

template<typename Node>
class iterator {
	Node* n;
public :
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

template<typename Node>
class const_iterator {
	const Node* n;
public :
	iterator() : n(nullptr) { }
	iterator(const Node* nd) : n(nd) { }
	iterator& operator ++() { n = n->next; return *this; }
	iterator& operator +()  { n = n->side; return *this; }
	iterator& operator --() { n = n->prev; return *this; }
	bool operator == (iterator it) { return n == it.n; }
	bool operator != (iterator it) { return !operator == (it); }
	const Node& operator *()   { return *n; }
	const Node* operator -> () { return n; }
};

struct Rule;

template<typename Node>
struct Term {
	Node* begin() { return iterator<Node>(b); }
	Node* end() { return iterator<Node>(); }
	const Node* cbegin() { return const_iterator<Node>(b); }
	const Node* cend() { return const_iterator<Node>(); }
	Node* rbegin() { return iterator<Node>(e); }
	Node* rend() { return iterator<Node>(); }
	const Node* crbegin() { return iterator<Node>(e); }
	const Node* crend() { return iterator<Node>(); }

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
	Term<List> term;
};

}} // mdl::rus

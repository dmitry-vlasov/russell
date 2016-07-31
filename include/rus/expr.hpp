#pragma once

#include "common.hpp"

namespace mdl { namespace rus {

#define END_MARKER ";;"

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

namespace node {

struct Expr;
template<class>
struct Tree;

}

namespace term {

struct Expr {
	typedef node::Expr Node;
	typedef iterator<Node> Iterator;
	typedef const_iterator<Node> ConstIterator;

	Expr(Node* f, Node* l, Rule* r) :
	first(f), last(l), rule(r), children() { }
	Expr(Node* v, Rule* r = nullptr) :
	first(v), last(v), rule(r), children() {
		if (rule) children.push_back(new Expr(v));
	}
	Expr(Node* f, Node* l, Rule* r, const vector<Expr*>& ch) :
	first(f), last(l), rule(r), children(ch) { }

	Iterator begin();
	Iterator end();
	ConstIterator begin() const;
	ConstIterator end() const;
	Iterator rbegin();
	Iterator rend();
	ConstIterator rbegin() const;
	ConstIterator rend() const;

	bool isvar() const;
	Symbol getvar() const;

	Expr* clone() const;
	bool operator == (const Expr& t) const;
	bool operator != (const Expr& t) const {
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
	vector<Expr*> children;
};

template<class T>
struct Tree {
	typedef node::Tree<T> Node;
	//typedef iterator<Node> Iterator;
	//typedef const_iterator<Node> ConstIterator;

	Tree(Node* f, Node* l, Rule* r) :
	first(f), last(), rule(r), children() { last.push_back(l); }
	Tree(Node* v, Rule* r = nullptr) :
	first(v), last(), rule(r), children() {
		last.push_back(v);
		if (rule) children.push_back(new Tree(v));
	}
	Tree(Node* f, Node* l, Rule* r, const vector<Tree*>& ch) :
	first(f), last(l), rule(r), children(ch) { last.push_back(l); }

	/*Iterator begin() { return Iterator(first); }
	Iterator end()   { return last->next ? Iterator(last->next) : Iterator(); }
	ConstIterator begin() const { return ConstIterator(first); }
	ConstIterator end() const { return last->next ? ConstIterator(last->next) : ConstIterator(); }
	Iterator rbegin() { return Iterator(last); }
	Iterator rend() { return first->prev ? Iterator(first->prev) : Iterator(); }
	ConstIterator rbegin() const { return ConstIterator(last); }
	ConstIterator rend() const { return first->prev ? ConstIterator(first->prev) : ConstIterator(); }*/

	bool isvar() const { return first == last.back() && first->symb.type && !rule; }
	Symbol getvar() const { return first->symb; }

	Tree* clone() const;
	bool operator == (const Tree& t) const;
	bool operator != (const Tree& t) const {
		return !operator == (t);
	}
	void destroy() {
		for(auto ch : children) {
			ch->destroy();
			delete ch;
		}
	}

	Node*         first;
	vector<Node*> last;
	Rule*         rule;
	vector<Tree*> children;
};


}

namespace node {

struct Expr {
	Expr() : symb(), next(nullptr), prev(nullptr) { }
	Expr(Symbol s) : symb(s), next(nullptr), prev(nullptr)  { }
	Expr(const Expr& ex) : symb(ex.symb), next(nullptr), prev(nullptr) { }
	Expr& operator = (const Expr& ex) {
		symb = ex.symb;
		next = nullptr;
		prev = nullptr;
		return *this;
	}
	Symbol symb;
	Expr*  next;
	Expr*  prev;
};

template<typename T>
struct Tree {
	Tree() : symb(), next(nullptr),
	prev(nullptr), side(nullptr), data() { }
	Tree(Symbol s) : symb(s), next(nullptr),
	prev(nullptr), side(nullptr), data() { }
	Tree(const Tree& tr) : symb(tr.symb), next(nullptr),
	prev(nullptr), side(nullptr), data() { }
	Tree& operator = (const Tree& tr) {
		symb = tr.symb;
		next = nullptr;
		prev = nullptr;
		side = nullptr;
		return *this;
	}
	Symbol symb;
	Tree*  next;
	Tree*  prev;
	Tree*  side;
	uint   level;
	T data;
};

} // namespace node

namespace sub {

struct Expr {
	~Expr() {
		for (auto p : sub) {
			p.second->destroy();
			delete p.second;
		}
	}
	bool join(Expr* s);
	term::Expr* find(Symbol v) {
		auto it = sub.find(v);
		if (it == sub.end()) return nullptr;
		else return it->second;
	}

	map<Symbol, term::Expr*> sub;
};

}

struct Expr;

template<typename T>
struct Tree {
	typedef node::Tree<T> Node;
	typedef term::Tree<T> Term;

	Tree() : root(nullptr), term(nullptr) { }
	~Tree();
	T& add(const Expr& ex);

	Node* root;
	Term* term;
};



struct Expr {
	typedef node::Expr Node;
	typedef term::Expr Term;
	typedef iterator<Node> Iterator;
	typedef const_iterator<Node> ConstIterator;

	Expr() : first(nullptr), last(nullptr), type(nullptr), term(nullptr) { }
	Expr(Symbol s) : first(nullptr), last(nullptr), type(s.type), term(nullptr) {
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
	Term* term;
};

inline iterator<node::Expr> begin(Expr& ex) { return ex.begin(); }
inline iterator<node::Expr> end(Expr& ex)   { return ex.end(); }
inline const_iterator<node::Expr> begin(const Expr& ex) { return ex.begin(); }
inline const_iterator<node::Expr> end(const Expr& ex) { return ex.end(); }
inline iterator<node::Expr> rbegin(Expr& ex) { return ex.rbegin(); }
inline iterator<node::Expr> rend(Expr& ex) { return ex.rend(); }
inline const_iterator<node::Expr> rbegin(const Expr& ex) { return ex.rbegin(); }
inline const_iterator<node::Expr> rend(const Expr& ex) { return ex.rend(); }

namespace term {

inline Expr::Iterator Expr::begin() { return Iterator(first); }
inline Expr::Iterator Expr::end()   { return last->next ? Iterator(last->next) : Iterator(); }
inline Expr::ConstIterator Expr::begin() const { return ConstIterator(first); }
inline Expr::ConstIterator Expr::end() const { return last->next ? ConstIterator(last->next) : ConstIterator(); }
inline Expr::Iterator Expr::rbegin() { return Iterator(last); }
inline Expr::Iterator Expr::rend() { return first->prev ? Iterator(first->prev) : Iterator(); }
inline Expr::ConstIterator Expr::rbegin() const { return ConstIterator(last); }
inline Expr::ConstIterator Expr::rend() const { return first->prev ? ConstIterator(first->prev) : ConstIterator(); }
inline bool Expr::isvar() const { return first == last && first->symb.type && !rule; }
inline Symbol Expr::getvar() const { return first->symb; }

inline Expr* Expr::clone() const {
	Expr* ret = new Expr(first, last, rule);
	for (auto ch : children)
		ret->children.push_back(ch->clone());
	return ret;
}
inline bool Expr :: operator == (const Expr& t) const {
	if (isvar() && t.isvar() && first->symb == t.first->symb)
		return true;
	if (rule != t.rule)
		return false;
	auto i_p = children.begin();
	auto i_q = t.children.begin();
	while (i_p != children.end()) {
		const Expr* ch_p = *i_p;
		const Expr* ch_q = *i_q;
		if (*ch_p != *ch_q) return false;
		++ i_p; ++ i_q;
	}
	return true;
}

}


sub::Expr* unify(const term::Expr* p, const term::Expr* q);
inline sub::Expr* unify(const Expr& ex1, const Expr& ex2) {
	return unify(ex1.term, ex2.term);
}
Expr assemble(const Expr& ex);
Expr assemble(const term::Expr* t);

namespace expr {
	void enqueue(Expr& ex);
	bool parse();
}

string show(const Expr&);
string show_ast(const term::Expr*, bool full = false);
inline string show_ast(const Expr& ex, bool full = false) {
	if (ex.term)
		return show_ast(ex.term, full);
	else
		return "<no ast>";
}

inline string show(const term::Expr& t) {
	deque<Symbol> symbs;
	for (auto it = t.rbegin(); it != t.rend(); -- it) {
		symbs.push_front(it->symb);
	}
	string str;
	for (auto s : symbs)
		str += show(s) + " ";
	return str;
}

inline string show(const sub::Expr& s) {
	string str;
	for (auto p : s.sub) {
		str += show(p.first, true) + " --> " + show_ast(p.second) + "\n";
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

template<class T, class N>
T* add_term(const term::Expr* st, map<node::Expr*, N*>& mp) {
	if (!st) return nullptr;
	assert(mp.find(st->first) != mp.end());
	assert(mp.find(st->last) != mp.end());
	T* tt = new T(mp[st->first], mp[st->last], st->rule);
	for (auto ch : st->children) {
		tt->children.push_back(add_term<T, N>(ch, mp));
	}
	return tt;
}

template<typename T>
T& Tree<T>::add(const Expr& ex) {
	assert(ex.first);
	map<node::Expr*, node::Tree<T>*> mp;
	node::Expr* m = ex.first;
	if (!root) {
		root = new node::Tree<T>(m->symb);
		mp[m] = root;
	}
	node::Tree<T>* n = root;
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
	add_term<term::Tree<T>, node::Tree<T>>(ex.term, mp);
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
	if (term) delete term;
}

void dump(const Symbol& s);
void dump(const Expr& ex);
void dump_ast(const Expr& ex);
void dump(const term::Expr* tm);
void dump_ast(const term::Expr* tm);
void dump(const sub::Expr& sb);


inline size_t memvol(const Symbol& s) {
	return 0;
}
inline size_t memvol(const term::Expr& t) {
	size_t vol = 0;
	vol += t.children.capacity();
	for (const term::Expr* ch : t.children)
		vol += memsize(*ch);
	return vol;
}
inline size_t memvol(const node::Expr& n) {
	return 0;
}
template<class T>
inline size_t memvol(const node::Tree<T>& n) {
	return memsize(n.data);
}
template<class T>
size_t memvol(const Tree<T>& t) {
	size_t s = 0;
	if (t.root) {
		vector<node::Tree<T>*> nodes;
		gather_tree_nodes(nodes, t.root);
		for (node::Tree<T>* n : nodes)
			s += memsize(*n);
	}
	return s;
}
size_t memvol(const Expr& ex);


}} // mdl::rus

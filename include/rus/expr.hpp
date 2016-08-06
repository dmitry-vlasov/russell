#pragma once

#include "common.hpp"

namespace mdl { namespace rus {

#define END_MARKER ";;"
#define UNDEF 0x7FFFFFFF

struct Type;

struct Symbol {
	Symbol(string s, Type* t = nullptr);
	Symbol(): lit(UNDEF), rep(false), type(nullptr) { }
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
	bool undef() const { return lit == UNDEF; }
	uint  lit:31;
	bool  rep:1;
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

struct Rule;
struct Expr;

namespace node {

	struct Expr;
	template<class>
	struct Tree;
}

namespace term {

struct Expr {
	typedef vector<Expr> Children;
	enum Kind { NONE, NODE, VAR };
	union Value {
		void*       none;
		Rule*       rule;
		node::Expr* var;
	};

	Expr() : kind(NONE), val(), children() { val.none = nullptr; }
	Expr(Rule* r) : kind(NODE)  { val.rule = r; }
	Expr(node::Expr* v) : kind(VAR), val(), children() { val.var = v; }
	Expr(Rule* r, const Children& ch) : kind(NODE), val(), children(ch) {
		val.rule = r;
	}
	bool operator == (const Expr& t) const;
	bool operator != (const Expr& t) const {
		return !operator == (t);
	}

	Kind kind;
	Value val;
	Children children;
};

template<class T>
struct Tree {
	Map<Rule*, vector<Tree<T>>> rules;
	Map<const rus::Expr*, node::Tree<T>*>     entries;
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
	bool join(Expr* s);
	bool has(Symbol v) { return sub.has(v); }
	Map<Symbol, term::Expr> sub;
};

}

template<typename T>
struct Tree {
	typedef node::Tree<T> Node;
	typedef term::Tree<T> Term;

	Tree() : root(nullptr), term() { }
	~Tree();
	T& add(const Expr& ex);

	Node* root;
	Term  term;
};



struct Expr {
	typedef node::Expr Node;
	typedef term::Expr Term;
	typedef iterator<Node> Iterator;
	typedef const_iterator<Node> ConstIterator;

	Expr() : first(nullptr), last(nullptr), type(nullptr), term() { }
	Expr(Symbol s) : first(nullptr), last(nullptr), type(s.type), term() {
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
	Term  term;
};

inline iterator<node::Expr> begin(Expr& ex) { return ex.begin(); }
inline iterator<node::Expr> end(Expr& ex)   { return ex.end(); }
inline const_iterator<node::Expr> begin(const Expr& ex) { return ex.begin(); }
inline const_iterator<node::Expr> end(const Expr& ex) { return ex.end(); }
inline iterator<node::Expr> rbegin(Expr& ex) { return ex.rbegin(); }
inline iterator<node::Expr> rend(Expr& ex) { return ex.rend(); }
inline const_iterator<node::Expr> rbegin(const Expr& ex) { return ex.rbegin(); }
inline const_iterator<node::Expr> rend(const Expr& ex) { return ex.rend(); }

sub::Expr* unify(const term::Expr& p, const term::Expr& q);
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
string show_ast(const term::Expr&, bool full = false);
inline string show_ast(const Expr& ex, bool full = false) {
	return show_ast(ex.term, full);
}

string show(const term::Expr& t, bool full = false);


inline string show(const sub::Expr& s) {
	string str;
	for (auto p : s.sub.m) {
		str += show(p.first, true) + " --> " + show_ast(p.second) + "\t ==\t"  + show(p.second) + "\n";
	}
	return str;
}

inline ostream& operator << (ostream& os, const Expr& ex) {
	os << show(ex);
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
void add_term(term::Tree<T>& tree_m, const term::Expr& expr_t, map<node::Expr*, N*>& mp, const Expr* ex) {
	if (expr_t.kind == term::Expr::VAR) {
		tree_m.entries[ex] = mp[expr_t.val.var];
		return;
	}
	if (!tree_m.rules.has(expr_t.val.rule)) {
		vector<term::Tree<T>>& tree_t = tree_m.rules[expr_t.val.rule];
		for_each(
			expr_t.children.begin(),
			expr_t.children.end(),
			[&tree_t](auto) mutable { tree_t.push_back(term::Tree<T>()); }
		);
	}
	vector<term::Tree<T>>& tree_t = tree_m.rules[expr_t.val.rule];
	auto tree_ch = tree_t.begin();
	for (auto& expr_ch : expr_t.children) {
		add_term(*tree_ch ++, expr_ch, mp, ex);
	}
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
	add_term(term, ex.term, mp, &ex);
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
	for (const term::Expr ch : t.children)
		vol += memvol(ch);
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

#pragma once

#include "expr.hpp"

namespace mdl { namespace rus {

#define END_MARKER ";;"

struct Type;

struct Symbol {
	Symbol(string s, Type* t = nullptr);
	Symbol(): lit(UNDEF_LIT), rep(false), type(nullptr) { }
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
	bool undef() const { return lit == UNDEF_LIT; }
	uint  lit:31;
	bool  rep:1;
	Type* type;
};

typedef vector<Symbol> Symbols;

string show(Symbol s, bool full = false);

inline ostream& operator << (ostream& os, Symbol s) {
	os << show(s);
	return os;
}

struct Rule;
struct Expr;

namespace node {
	template<class>
	struct Tree;
}

namespace term {

struct Expr {
	typedef vector<Expr> Children;
	enum Kind { NODE, VAR };
	union Value {
		Rule*   rule;
		Symbol* var;
	};

	Expr() : kind(VAR), val(), children() { val.var = nullptr; }
	Expr(Rule* r) : kind(NODE)  { val.rule = r; }
	Expr(Symbol* v) : kind(VAR), val(), children() { val.var = v; }
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
	Map<const rus::Expr*, node::Tree<T>*> entries;
};

}

namespace node {

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
	typedef term::Expr Term;

	Expr() : type(nullptr), term(), symbols() { }
	Expr(Symbol s) : type(s.type), term(), symbols() {
		symbols.push_back(s);
	}
	void push_back(Symbol s) {
		symbols.push_back(s);
	}
	void push_front(Symbol s) {
		symbols.insert(symbols.begin(), s);
	}
	Symbol pop_back() {
		Symbol s = symbols.back();
		symbols.pop_back();
		return s;
	}
	bool operator == (const Expr& ex) const {
		return (type == ex.type) && (symbols == ex.symbols);
	}
	bool operator != (const Expr& ex) const {
		return !operator == (ex);
	}

	Type*   type;
	Term    term;
	Symbols symbols;
};

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
void add_term(term::Tree<T>& tree_m, const term::Expr& expr_t, map<const Symbol*, N*>& mp, const Expr* ex) {
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
	assert(ex.symbols.size());
	map<const Symbol*, node::Tree<T>*> mp;
	Symbols::const_iterator it = ex.symbols.begin();
	Symbols::const_iterator last = ex.symbols.end() - 1;
	if (!root) {
		root = new node::Tree<T>(*it);
		mp[&(*it)] = root;
	}
	node::Tree<T>* n = root;
	while (true) {
		while (n->side && *it != n->symb)
			n = n->side;
		if (n->symb == *it && (it != last) && n->next) {
			mp[&(*it)] = n;
			n = n->next;
			++it;
		} else break;
	}
	if (n->symb != *it) {
		n = new_side(n, *it);
		mp[&(*it)] = n;
	}
	while (it != last) {
		++ it;
		n = new_next(n, *it);
		mp[&(*it)] = n;
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

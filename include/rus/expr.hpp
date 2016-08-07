#pragma once

#include "expr.hpp"

namespace mdl { namespace rus {

#define END_MARKER ";;"

struct Type;

struct Symbol : public mdl::Symbol {
	Symbol(string s, Type* t = nullptr);
	Symbol() : mdl::Symbol(), type(nullptr) { }
	Symbol(uint l): mdl::Symbol(l), type(nullptr) { }
	Symbol(const mdl::Symbol s, bool v = false) :
	mdl::Symbol(s.lit, v), type(nullptr) { }
	Symbol(const mdl::Symbol s, Type* tp, bool v = false) :
	mdl::Symbol(s.lit, v), type(tp) { }

	bool operator == (const Symbol& s) const {
		return mdl::Symbol::operator == (s) && type == s.type;
	}
	bool operator != (const Symbol& s) const {
		return !operator ==(s);
	}
	bool operator < (const Symbol& s) const {
		return
			type == s.type ?
			mdl::Symbol::operator < (s.lit) :
			type < s.type;
	}
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
	struct PTree;
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
	Expr(Symbol& v) : kind(VAR), val(), children() { val.var = &v; }
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
struct PTree {
	Map<Rule*, vector<PTree<T>>> rules;
	Map<const rus::Expr*, node::PTree<T>*> entries;
};

template<class T>
struct Tree {
	Map<Rule*, vector<Tree<T>>>    rules;
	Map<const rus::Expr*, const Symbol*> entries;
};

}

namespace node {

template<typename T>
struct PTree {
	PTree() : symb(), next(nullptr),
	prev(nullptr), side(nullptr), data() { }
	PTree(Symbol s) : symb(s), next(nullptr),
	prev(nullptr), side(nullptr), data() { }
	PTree(const PTree& tr) : symb(tr.symb), next(nullptr),
	prev(nullptr), side(nullptr), data() { }
	PTree& operator = (const PTree& tr) {
		symb = tr.symb;
		next = nullptr;
		prev = nullptr;
		side = nullptr;
		return *this;
	}
	Symbol symb;
	PTree*  next;
	PTree*  prev;
	PTree*  side;
	uint   level;
	T data;
};

template<typename T>
struct Tree {
	struct Node {
		Tree<T> tree;
		uint    level;
		T       data;
	};
	typedef mdl::Map<Symbol, Node> Map;
	Map map;
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
struct PTree {
	typedef node::PTree<T> Node;
	typedef term::PTree<T> Term;

	PTree() : root(nullptr), term() { }
	~PTree();
	T& add(const Expr& ex);

	Node* root;
	Term  term;
};

template<typename T>
struct Tree {
	typedef node::Tree<T> Map;
	typedef term::Tree<T> Term;
	T& add(const Expr& ex);

	Map  root;
	Term term;
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
void add_term(term::PTree<T>& tree_m, const term::Expr& expr_t, map<const Symbol*, N*>& mp, const Expr* ex) {
	if (expr_t.kind == term::Expr::VAR) {
		tree_m.entries[ex] = mp[expr_t.val.var];
		return;
	}
	if (!tree_m.rules.has(expr_t.val.rule)) {
		vector<term::PTree<T>>& tree_t = tree_m.rules[expr_t.val.rule];
		for_each(
			expr_t.children.begin(),
			expr_t.children.end(),
			[&tree_t](auto) mutable { tree_t.push_back(term::PTree<T>()); }
		);
	}
	vector<term::PTree<T>>& tree_t = tree_m.rules[expr_t.val.rule];
	auto tree_ch = tree_t.begin();
	for (auto& expr_ch : expr_t.children) {
		add_term(*tree_ch ++, expr_ch, mp, ex);
	}
}

template<typename T>
T& PTree<T>::add(const Expr& ex) {
	assert(ex.symbols.size());
	map<const Symbol*, node::PTree<T>*> mp;
	Symbols::const_iterator it = ex.symbols.begin();
	Symbols::const_iterator last = ex.symbols.end() - 1;
	if (!root) {
		root = new node::PTree<T>(*it);
		mp[&(*it)] = root;
	}
	node::PTree<T>* n = root;
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







template<class T>
void add_term(term::Tree<T>& tree_m, const term::Expr& expr_t, map<const Symbol*, const Symbol*>& mp, const Expr* ex) {
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
	map<const Symbol*, const Symbol*> mp;
	Map& m = root;
	typename Map::Node* n = nullptr;
	for (auto& s : ex.symbols) {
		Map& new_m = m.map[s].tree;
		auto i = m.map.m.find(s);
		mp[&s] = &i->first;
		n = &i->second;
		m = new_m;
	}
	assert(n);
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
PTree<T>::~PTree() {
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
inline size_t memvol(const node::PTree<T>& n) {
	return memsize(n.data);
}
template<class T>
size_t memvol(const PTree<T>& t) {
	size_t s = 0;
	if (t.root) {
		vector<node::PTree<T>*> nodes;
		gather_tree_nodes(nodes, t.root);
		for (node::PTree<T>* n : nodes)
			s += memsize(*n);
	}
	return s;
}
size_t memvol(const Expr& ex);


}} // mdl::rus

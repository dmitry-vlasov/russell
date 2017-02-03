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
	Symbol(mdl::Symbol s, Type* tp, bool v = false) :
	mdl::Symbol(s.lit, v), type(tp) { }
	Symbol(const Symbol& s) : mdl::Symbol(s), type(s.type) { }

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
	struct Hash {
		typedef size_t result_type;
		typedef Symbol argument_type;
		size_t operator() (Symbol s) const {
			return hash(s.lit);
		}
	private:
		static std::hash<uint> hash;
	};
};

typedef vector<Symbol> Symbols;

string show(Symbol s, bool full = false);

inline ostream& operator << (ostream& os, Symbol s) {
	os << show(s);
	return os;
}

struct Rule;

struct Tree {
	typedef vector<unique_ptr<Tree>> Children;
	enum Kind { NODE, VAR};

private:
	struct Node {
		Node(Rule* r = nullptr) : rule(r), children() { }
		Node(Rule* r, const Children& ch) : rule(r), children() {
			children.reserve(ch.size());
			for (auto& c : ch) children.push_back(make_unique<Tree>(*c.get()));
		}
		Node(const Node& n) : rule(n.rule), children() {
			children.reserve(n.children.size());
			for (auto& c : n.children) children.push_back(make_unique<Tree>(*c.get()));
		}
		Node(Node&& n) : rule(n.rule), children(std::move(n.children)) { }
		Node(Rule* r, Children&& ch) : rule(r), children(std::move(ch)) { }
		Node(Rule* r, Tree* ch) : rule(r), children() {
			children.push_back(unique_ptr<Tree>(ch));
		}
		Rule*    rule;
		Children children;
	};
	union Value {
		Value() : var(nullptr) { }
		Value(Node* n) : node(n) { }
		Value(Symbol* v) : var(v) { }
		Node*   node;
		Symbol* var;
	};

public :
	Tree(const Symbol& v) : kind(VAR), val(new Symbol(v)) { }
	Tree(Rule* r, const Children& ch) : kind(NODE), val(new Node(r, ch)) { }
	Tree(Rule* r, Tree* ch) : kind(NODE), val(new Node(r, ch)) { }
	Tree(const Tree& ex) : kind(ex.kind), val() {
		switch (kind) {
		case NODE: val.node = new Node(*ex.val.node);  break;
		case VAR:  val.var  = new Symbol(*ex.val.var); break;
		}
	}
	Tree(Tree&& ex) : kind(ex.kind), val(ex.val) { ex.val.var = nullptr; }
	~Tree() { delete_val(); }

	void operator = (Tree&& ex) {
		delete_val();
		kind = ex.kind;
		val = ex.val;
		ex.val.var = nullptr;
	}
	void operator = (const Tree& ex) {
		delete_val();
		kind = ex.kind;
		switch (kind) {
		case NODE: val.node = new Node(*ex.val.node);  break;
		case VAR:  val.var  = new Symbol(*ex.val.var); break;
		}
	}
	bool operator == (const Tree& e) const {
		if (kind != e.kind) return false;
		switch (kind) {
		case NODE:
			if (val.node->rule != e.val.node->rule) return false;
			return std::equal(
				val.node->children.begin(),val.node->children.end(),
				e.val.node->children.begin(), e.val.node->children.end(),
				[] (auto const& c1, auto const& c2) -> bool { return *c1 == *c2; }
			);
		case VAR: return *val.var == *e.val.var;
		}
		return true;
	}
	bool operator != (const Tree& e) const {
		return !operator == (e);
	}

	Kind kind;

	Symbol*& var() { assert(kind == VAR); return val.var; }
	Rule*& rule() { assert(kind == NODE); return val.node->rule; }
	Children& children() { assert(kind == NODE); return val.node->children; }
	Type* type();

	const Symbol* var() const { assert(kind == VAR); return val.var; }
	const Rule* rule() const { assert(kind == NODE); return val.node->rule; }
	const Children& children() const { assert(kind == NODE); return val.node->children; }
	const Type* type() const;

private:
	Value val;
	void delete_val() {
		if (!val.var) return;
		switch (kind) {
		case NODE: delete val.node; break;
		case VAR:  delete val.var;  break;
		}
	}
};

struct Expr {
	Expr() : type(nullptr), tree(), symbols() { }
	Expr(Symbol s) : type(s.type), tree(), symbols() { symbols.push_back(s); }
	Expr(const Expr& ex) : type(ex.type), tree(), symbols (ex.symbols) {
		if (ex.tree) tree.reset(new Tree(*ex.tree));
	}
	Expr(Expr&& ex) : type(ex.type), tree(std::move(ex.tree)), symbols (std::move(ex.symbols)) { }

	void operator = (const Expr& ex) {
		type = ex.type;
		tree = make_unique<Tree>(*ex.tree.get());
		symbols = ex.symbols;
	}

	void operator = (Expr&& ex) {
		type = ex.type;
		tree = std::move(ex.tree);
		symbols = std::move(ex.symbols);
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

	Type*            type;
	unique_ptr<Tree> tree;
	Symbols          symbols;
};

struct Rules {
	struct Node;
	typedef vector<Node> Map;
	Rule*& add(const Expr& ex);
	Map map;
};

struct Rules::Node {
	Node(Symbol s) : symb(s), tree(), level(), rule(nullptr) { }
	Symbol symb;
	Rules  tree;
	uint   level;
	Rule*  rule;
};

inline Rule*& Rules::add(const Expr& ex) {
	assert(ex.symbols.size());
	Rules* m = this;
	Node* n = nullptr;
	for (const Symbol& s : ex.symbols) {
		bool new_symb = true;
		for (Node& p : m->map) {
			if (p.symb == s) {
				n = &p;
				m = &p.tree;
				new_symb = false;
				break;
			}
		}
		if (new_symb) {
			if (m->map.size()) m->map.back().symb.fin = false;
			m->map.push_back(Node(s));
			n = &m->map.back();
			n->symb.fin = true;
			m = &n->tree;
		}
	}
	return n->rule;
}


string show(const Rules& tr);

struct Substitution {
	Substitution() : sub() { }
	Substitution(Symbol v, Tree* t) : sub() { sub[v].reset(t); }
	bool join(Substitution* s) {
		for (auto& p : s->sub) {
			auto it = sub.find(p.first);
			if (it != sub.end()) {
				if (*(*it).second != *p.second) return false;
			} else {
				sub[p.first].reset(new Tree(*p.second));
			}
		}
		return true;
	}
	map<Symbol, unique_ptr<Tree>> sub;
};


Substitution* unify(const Tree* p, const Tree* q);
inline Substitution* unify(const Expr& ex1, const Expr& ex2) {
	return unify(ex1.tree.get(), ex2.tree.get());
}
Expr assemble(const Expr& ex);
Expr assemble(const Tree* t);

namespace expr {
	void enqueue(Expr& ex);
	bool parse();
}

string show(const Expr&);
string show_ast(const Tree&, bool full = false);
inline string show_ast(const Expr& ex, bool full = false) {
	return show_ast(*ex.tree, full);
}

string show(const Tree& t, bool full = false);


inline string show(const Substitution& s) {
	string str;
	for (auto& p : s.sub) {
		str += show(p.first, true) + " --> " + show_ast(*p.second) + "\t ==\t"  + show(*p.second) + "\n";
	}
	return str;
}

inline ostream& operator << (ostream& os, const Expr& ex) {
	os << show(ex);
	return os;
}

void dump(const Symbol& s);
void dump(const Expr& ex);
void dump_ast(const Expr& ex);
void dump(const Tree* tm);
void dump_ast(const Tree* tm);
void dump(const Substitution& sb);


inline size_t memvol(const Symbol& s) {
	return 0;
}
inline size_t memvol(const Tree& t) {
	if (t.kind != Tree::NODE) return 0;
	size_t vol = 0;
	vol += t.children().capacity();
	for (auto& ch : t.children())
		vol += memvol(*ch.get());
	return vol;
}

size_t memvol(const Expr& ex);
size_t memvol(const Rules&);

}} // mdl::rus

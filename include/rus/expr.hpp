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

namespace term {

struct Tree {
	typedef vector<Tree*> Children;
	enum Kind { NODE, VAR};

private:
	struct Node {
		Node(Rule* r = nullptr) : rule(r), children() { }
		Node(Rule* r, const Children& ch) : rule(r), children(ch) { }
		Node(const Node& n) : rule(n.rule), children() {
			for (auto ch : n.children) children.push_back(new Tree(*ch));
		}
		~Node() { for (auto ch : children) delete ch; }
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
	Tree() : kind(NODE), val(new Node()) { }
	Tree(Rule* r) : kind(NODE), val(new Node(r))  { }
	Tree(const Symbol& v) : kind(VAR), val(new Symbol(v)) { }
	Tree(Rule* r, const Children& ch) : kind(NODE), val(new Node(r, ch)) { }
	~Tree() { delete_val(); }
	Tree(const Tree& ex) : kind(ex.kind), val() {
		switch (kind) {
		case NODE: val.node = new Node(*ex.val.node);  break;
		case VAR:  val.var  = new Symbol(*ex.val.var); break;
		}
	}
	Tree(Tree&& ex) : kind(ex.kind), val(ex.val) { ex.val.var = nullptr; }

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

}

struct Substitution {
	~Substitution() { for (auto p : sub) delete p.second; }
	bool join(Substitution* s);
	map<Symbol, term::Tree*> sub;
};

struct Expr {
	typedef term::Tree Term;

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

struct Rules {
	struct Node;
	typedef vector<Node> Map;
	Rule*& add(const Expr& ex);
	Map map;
};

struct Rules::Node {
	Node(Symbol s) : symb(s), tree(), level(), rule(nullptr) { }
	Symbol   symb;
	Rules tree;
	uint     level;
	Rule*    rule;
};

string show(const Rules& tr);



Substitution* unify(const term::Tree* p, const term::Tree* q);
inline Substitution* unify(const Expr& ex1, const Expr& ex2) {
	return unify(&ex1.term, &ex2.term);
}
Expr assemble(const Expr& ex);
Expr assemble(const term::Tree* t);

namespace expr {
	void enqueue(Expr& ex);
	bool parse();
}

string show(const Expr&);
string show_ast(const term::Tree&, bool full = false);
inline string show_ast(const Expr& ex, bool full = false) {
	return show_ast(ex.term, full);
}

string show(const term::Tree& t, bool full = false);


inline string show(const Substitution& s) {
	string str;
	for (auto p : s.sub) {
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
void dump(const term::Tree* tm);
void dump_ast(const term::Tree* tm);
void dump(const Substitution& sb);


inline size_t memvol(const Symbol& s) {
	return 0;
}
inline size_t memvol(const term::Tree& t) {
	if (t.kind != term::Tree::NODE) return 0;
	size_t vol = 0;
	vol += t.children().capacity();
	for (const term::Tree* ch : t.children())
		vol += memvol(*ch);
	return vol;
}

size_t memvol(const Expr& ex);
size_t memvol(const Rules&);

}} // mdl::rus

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
struct Expr;

namespace node {
	template<class>
	struct PTree;
}

namespace term {

struct Expr {
	typedef vector<Expr> Children;
	enum Kind { NODE, VAR };

private:
	struct Node {
		Node(Rule* r) : rule(r), children() { }
		Node(Rule* r, const Children& ch) : rule(r), children(ch) { }
		Rule*    rule;
		Children children;
	};
	union Value {
		Value() : node(nullptr) { }
		Value(Node* n) : node(n) { }
		Value(Symbol* v) : var(v) { }
		Node*   node;
		Symbol* var;
	};

public :
	Expr(Kind k = NODE) : kind(k), val(k == NODE ? new Node(nullptr) : nullptr) { }
	Expr(Rule* r) : kind(NODE), val(new Node(r))  { }
	Expr(Symbol& v) : kind(VAR), val(&v) { }
	Expr(Rule* r, const Children& ch) : kind(NODE), val(new Node(r, ch)) {
	}
	bool operator == (const Expr& t) const;
	bool operator != (const Expr& t) const {
		return !operator == (t);
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
};

template<class T>
struct Tree {
	map<Rule*, vector<Tree<T>>> rules;
	map<const rus::Expr*, const Symbol*> entries;
};

}

struct Substitution {
	bool join(Substitution* s);
	map<Symbol, term::Expr> sub;
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

Substitution* unify(const term::Expr& p, const term::Expr& q);
inline Substitution* unify(const Expr& ex1, const Expr& ex2) {
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


inline string show(const Substitution& s) {
	string str;
	for (auto p : s.sub) {
		str += show(p.first, true) + " --> " + show_ast(p.second) + "\t ==\t"  + show(p.second) + "\n";
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
void dump(const term::Expr* tm);
void dump_ast(const term::Expr* tm);
void dump(const Substitution& sb);


inline size_t memvol(const Symbol& s) {
	return 0;
}
inline size_t memvol(const term::Expr& t) {
	if (t.kind != term::Expr::NODE) return 0;
	size_t vol = 0;
	vol += t.children().capacity();
	for (const term::Expr ch : t.children())
		vol += memvol(ch);
	return vol;
}

size_t memvol(const Expr& ex);
size_t memvol(const Rules&);

}} // mdl::rus

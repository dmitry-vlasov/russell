#pragma once

#include "expr.hpp"

namespace mdl { namespace rus {

#define END_MARKER ";;"

typedef mdl::Token<Source> Token;

struct Type;
struct Rule;

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

struct Tree {
	typedef vector<unique_ptr<Tree>> Children;
	enum Kind { NODE, VAR};

	struct Node {
		Node(Rule* r = nullptr);
		Node(const Node& n);
		Node(Node&& n);
		Node(Rule* r, const Children& ch);
		Node(Rule* r, Children&& ch);
		Node(Rule* r, Tree* ch);
		~Node();
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

	Tree(const Symbol& v);
	Tree(Rule* r, const Children& ch);
	Tree(Rule* r, Tree* ch);
	Tree(const Tree& ex);
	Tree(Tree&& ex);
	~Tree();

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
	Expr(const Symbols& ss) : type(nullptr), tree(), symbols(ss) { }
	Expr(const Expr& ex) : type(ex.type), tree(), symbols (ex.symbols) {
		if (ex.tree) tree.reset(new Tree(*ex.tree));
	}
	Expr(Expr&& ex) : type(ex.type), tree(std::move(ex.tree)), symbols (std::move(ex.symbols)) { }

	void operator = (const Expr& ex) {
		type = ex.type;
		if (ex.tree) tree.reset(new Tree(*ex.tree));
		else tree.reset();
		symbols = ex.symbols;
		token = ex.token;
	}

	void operator = (Expr&& ex) {
		type = ex.type;
		tree = std::move(ex.tree);
		symbols = std::move(ex.symbols);
		token = ex.token;
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
	Token            token;
};

struct Rules {
	struct Node;
	typedef vector<Node*> Map;
	void add(const Expr& ex, uint id);
	~Rules();
	Map map;
};

struct Rules::Node {
	Node(Symbol s) : symb(s), tree(), level(), rule(nullptr) { }
	~Node();
	Symbol symb;
	Rules  tree;
	uint   level;
	Rule*  rule;
};


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

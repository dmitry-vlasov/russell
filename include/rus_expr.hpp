#pragma once

#include "rus_sys.hpp"

namespace mdl { namespace rus {

#define END_MARKER ";;"

typedef mdl::Token<Source> Token;
typedef mdl::Tokenable<Source> Tokenable;
typedef mdl::Id<Source> Id;

struct Type;
struct Rule;

struct Symbol : public mdl::Symbol {
	Symbol() : mdl::Symbol() { }
	Symbol(uint l) : mdl::Symbol(l) { }
	Symbol(uint l, Type* t) : mdl::Symbol(l), val(t) { var = true; }
	Symbol(uint l, Const* c): mdl::Symbol(l), val(c) { cst = true; }
	Symbol(const Symbol& s) : mdl::Symbol(s) {
		if (s.var)
			val.type = new User<Type>(*s.val.type);
		else if (s.cst)
			val.constant = new User<Const>(*s.val.constant);
	}
	Symbol(Symbol&& s) : mdl::Symbol(s) {
		if (s.var)
			val.type = s.val.type;
		else if (s.cst)
			val.constant = s.val.constant;
		s.var = false;
		s.cst = false;
		s.val.type = nullptr;
	}
	~Symbol() { clear(); }

	void operator = (const Symbol& s) {
		clear();
		mdl::Symbol::operator=(s);
		if (s.var)
			val.type = new User<Type>(*s.val.type);
		else if (s.cst)
			val.constant = new User<Const>(*s.val.constant);
	}
	void operator = (Symbol&& s) {
		clear();
		mdl::Symbol::operator=(s);
		if (s.var)
			val.type = s.val.type;
		else if (s.cst)
			val.constant = s.val.constant;
		s.var = false;
		s.cst = false;
		s.val.type = nullptr;
	}

	Type* type() { return var ? val.type->get() : nullptr; }
	Const* constant() { return cst ? val.constant->get() : nullptr; }
	const Type* type() const { return var ? val.type->get() : nullptr; }
	const Const* constant() const { return cst ? val.constant->get() : nullptr; }

	void set_type(Id i) {
		clear();
		val.type = new User<Type>(i);
		var = true;
	}

	void set_type(Type* t) {
		clear();
		val.type = new User<Type>(t);
		var = true;
	}

	void set_const(Const* c) {
		clear();
		val.constant = new User<Const>(c);
		cst = true;
	}

	struct Hash {
		typedef size_t result_type;
		typedef Symbol argument_type;
		size_t operator() (Symbol s) const {
			return hash(s.lit);
		}
	private:
		static std::hash<uint> hash;
	};

private:
	union Value {
		Value(): constant(nullptr) { }
		Value(Type* t) : type(new User<Type>(t)) { }
		Value(Const* c) : constant(new User<Const>(c)) { }
		User<Const>* constant;
		User<Type>*  type;
	};
	Value val;

	void clear() {
		if (var)
			delete val.type;
		else if (cst)
			delete val.constant;
		var = false;
		cst = false;
	}
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
		User<Rule> rule;
		Children   children;
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
	Children& children() { assert(kind == NODE); return val.node->children; }
	Type* type();

	const Symbol* var() const { assert(kind == VAR); return val.var; }
	const Rule* rule() const { assert(kind == NODE); return val.node->rule.get(); }
	const Children& children() const { assert(kind == NODE); return val.node->children; }
	const Type* type() const;

private:
	union Value {
		Value() : var(nullptr) { }
		Value(Node* n) : node(n) { }
		Value(Symbol* v) : var(v) { }
		Node*   node;
		Symbol* var;
	};

	Value val;
	void delete_val() {
		if (!val.var) return;
		switch (kind) {
		case NODE: delete val.node; break;
		case VAR:  delete val.var;  break;
		}
	}
};

struct Expr : public Tokenable {
	Expr(const Token& t = Token()) : Tokenable(t), tree(), symbols() { }
	Expr(Symbol s, const Token& t = Token()) : Tokenable(t), type(s.type()), tree(), symbols() { symbols.push_back(s); }
	Expr(const Symbols& ss, const Token& t = Token()) : Tokenable(t), tree(), symbols(ss) { }
	Expr(Id tp, Symbols&& ex, const Token& t = Token()) : Tokenable(t), type(tp), symbols(std::move(ex)) { }
	Expr(const Expr& ex) : Tokenable(ex), type(ex.type), tree(), symbols (ex.symbols) {
		if (ex.tree) tree.reset(new Tree(*ex.tree));
	}
	Expr(Expr&& ex) : Tokenable(ex.token), type(ex.type), tree(std::move(ex.tree)), symbols (std::move(ex.symbols)) { }

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

	typedef Symbols::iterator iterator;
	typedef Symbols::const_iterator const_iterator;

	iterator begin() { return symbols.begin(); }
	iterator end() { return symbols.end(); }

	const_iterator begin() const { return symbols.cbegin(); }
	const_iterator end() const { return symbols.cend(); }

	User<Type>       type;
	unique_ptr<Tree> tree;
	Symbols          symbols;
};

struct Rules {
	struct Node;
	typedef vector<Node*> Map;
	void add(const Expr& ex, uint id);
	~Rules();
	Map map;
};

struct Rules::Node {
	Node(Symbol s) : symb(s) { }
	Symbol     symb;
	Rules      tree;
	User<Rule> rule;
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
//Expr assemble(const Expr& ex);
//Expr assemble(const Tree* t);

Expr apply(const Substitution*, const Expr&);

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

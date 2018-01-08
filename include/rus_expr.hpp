#pragma once

#include "rus_sys.hpp"
#include "smm_expr.hpp"

namespace mdl { namespace rus {

#define END_MARKER ";;"

typedef mdl::Token<Source> Token;
typedef mdl::Tokenable<Source> Tokenable;
typedef mdl::Id<Source> Id;

struct Type;
struct Rule;

struct Literal {
	enum Kind { VAR, CONST, NONE };
	Literal(): lit(undef()), var(false), cst(false), end(false), rep(false), fin(false) { }
	Literal(uint l, bool v = false) : lit(l), var(v), cst(false), end(false), rep(false), fin(false) { }
	Literal(const Literal& s) : lit(s.lit), var(s.var), cst(s.cst), end(s.end), rep(s.rep), fin(s.fin) { }

	bool operator == (const Literal& s) const { return lit == s.lit; }
	bool operator != (const Literal& s) const { return !operator ==(s); }
	bool operator < (const Literal& s) const { return lit < s.lit; }
	bool is_undef() const { return lit == undef(); }
	static bool is_undef(uint lit) { return lit == undef(); }
	static uint undef() { return 0x07FFFFFF; }
	Kind kind() const {
		if (var && !cst) return VAR;
		if (cst && !var) return CONST;
		return NONE;
	}
	void set_kind(Kind k) {
		switch (k) {
		case VAR:   var = true; cst = false;  rep = true;  break;
		case CONST: var = false; cst = true;  rep = false; break;
		default:    var = false; cst = false; rep = false; break;
		}
	}

	uint lit:27;

	// Flags
	bool var:1; //< is variable
	bool cst:1; //< is constant
	bool end:1; //< is end of an expression
	bool rep:1; //< is replaceable variable
	bool fin:1; //< final node in a tree (in a horizontal iteration)
};

struct Symbol : public Literal {
	Symbol() : Literal() { }
	Symbol(uint l) : Literal(l) { }
	Symbol(uint l, Id i, Kind k) : Literal(l), val(i, k) { set_kind(k); }
	Symbol(const Symbol& s) : Literal(s) {
		if (s.var)
			val.type = new User<Type>(*s.val.type);
		else if (s.cst)
			val.constant = new User<Const>(*s.val.constant);
	}
	Symbol(Symbol&& s) : Literal(s) {
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
		Literal::operator=(s);
		switch (s.kind()) {
		case VAR:   val.type = new User<Type>(*s.val.type);          break;
		case CONST: val.constant = new User<Const>(*s.val.constant); break;
		}
	}
	void operator = (Symbol&& s) {
		clear();
		Literal::operator=(s);
		switch (s.kind()) {
		case VAR:   val.type = s.val.type;         break;
		case CONST: val.constant = s.val.constant; break;
		}
		s.set_kind(NONE);
		s.val.type = nullptr;
	}

	uint type_id() { return var ? val.type->id() : UNDEF_UINT; }
	uint constant_id() { return cst ? val.constant->id() : UNDEF_UINT; }
	Type* type() { return var ? val.type->get() : nullptr; }
	Const* constant() { return cst ? val.constant->get() : nullptr; }
	const Type* type() const { return var ? val.type->get() : nullptr; }
	const Const* constant() const { return cst ? val.constant->get() : nullptr; }

	void set_type(Id i) {
		clear();
		val.type = new User<Type>(i);
		var = true;
		rep = true;
	}

	void set_type(uint t) {
		clear();
		if (t == UNDEF_UINT) return;
		val.type = new User<Type>(t);
		var = true;
		rep = true;
	}

	void set_const() {
		clear();
		if (is_undef()) return;
		val.constant = new User<Const>(lit);
		cst = true;
		rep = false;
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
		Value(Id i, Kind k) {
			switch (k) {
			case VAR:   type = new User<Type>(i);      break;
			case CONST: constant = new User<Const>(i); break;
			default: break;
			};
		}
		User<Const>* constant;
		User<Type>*  type;
	};
	Value val;

	void clear() {
		switch (kind()) {
		case VAR:   delete val.type;     break;
		case CONST: delete val.constant; break;
		}
		val.type = nullptr;
		set_kind(NONE);
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
	enum Kind { NODE, VAR, NONE};

	struct Node {
		Node(Id = Id());
		Node(const Node& n);
		Node(Node&& n);
		Node(Id i, const Children& ch);
		Node(Id i, Children&& ch);
		Node(Id i, Tree* ch);
		~Node();
		User<Rule> rule;
		Children   children;
	};

	Tree();
	Tree(const Symbol& v);
	Tree(Id i, const Children& ch);
	Tree(Id i, Tree* ch);
	Tree(const Tree& ex);
	Tree(Tree&& ex);
	~Tree();

	void operator = (Tree&& ex) {
		delete_val();
		kind = ex.kind;
		val = ex.val;
		ex.val.var = nullptr;
		ex.kind = NONE;
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
	bool leaf() const {
		return kind == VAR || !children().size();
	}

	Kind kind;

	Symbol*& var() { assert(kind == VAR); return val.var; }
	Children& children() { assert(kind == NODE); return val.node->children; }
	Type* type();

	const Symbol* var() const { assert(kind == VAR); return val.var; }
	const Rule* rule() const { assert(kind == NODE); return val.node->rule.get(); }
	const Children& children() const { assert(kind == NODE); return val.node->children; }
	const Type* type() const;
	uint arity() const {
		switch (kind) {
		case NODE: return val.node->children.size();
		case VAR:  return 0;
		default:   return -1;
		}
	}

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

class Expr;

namespace expr { void parse_LL(Expr*); }

struct Expr : public Tokenable {
	Expr(const Token& t = Token()) : Tokenable(t), tree(), symbols() { }
	Expr(Symbol s, const Token& t = Token()) : Tokenable(t), type(s.type()), tree(), symbols() { symbols.push_back(s); }
	Expr(const Symbols& ss, const Token& t = Token()) : Tokenable(t), tree(), symbols(ss) { }
	Expr(Id tp, Symbols&& ex, const Token& t = Token()) : Tokenable(t), type(tp), symbols(std::move(ex)) { }
	Expr(Id tp, Symbols&& ex, Tree&& tr, const Token& t = Token()) : Tokenable(t), type(tp), tree(std::move(tr)), symbols(std::move(ex)) { }
	Expr(const Expr& ex) : Tokenable(ex), type(ex.type), tree(ex.tree), symbols (ex.symbols) { }
	Expr(Expr&& ex) : Tokenable(ex.token), type(ex.type), tree(std::move(ex.tree)), symbols (std::move(ex.symbols)) { }

	void operator = (const Expr& ex) {
		type = ex.type;
		tree = ex.tree;
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
	void parse() {
		expr::parse_LL(this);
	}

	typedef Symbols::iterator iterator;
	typedef Symbols::const_iterator const_iterator;

	iterator begin() { return symbols.begin(); }
	iterator end() { return symbols.end(); }

	const_iterator begin() const { return symbols.cbegin(); }
	const_iterator end() const { return symbols.cend(); }

	User<Type> type;
	Tree       tree;
	Symbols    symbols;
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
	Substitution(bool ok = true) : sub_(), ok_(ok) { }
	Substitution(Symbol v, Symbol t) : sub_(), ok_(true) {
		sub_[v] = t;
	}
	Substitution(Symbol v, const Tree& t) : sub_(), ok_(true) {
		sub_[v] = t;
	}
	Substitution(const Substitution& s) : sub_(), ok_(s.ok_) {
		operator =(s);
	}
	Substitution(Substitution&& s) : sub_(), ok_(s.ok_) {
		operator =(s);
	}
	void operator = (const Substitution& s) {
		ok_ = s.ok_;
		if (ok_) for (const auto& p : s.sub_)
			sub_[p.first] = p.second;
	}
	void operator = (Substitution&& s) {
		ok_ = s.ok_;
		if (ok_) for (auto& p : s.sub_)
			sub_[p.first] = std::move(p.second);
		s.sub_.clear();
		s.ok_ = true;
	}
	bool join(Symbol v, Symbol t) {
		return join(v, Tree(t));
	}
	bool join(Symbol v, const Tree& t) {
		if (!ok_) return false;
		auto it = sub_.find(v);
		if (it != sub_.end()) {
			if ((*it).second != t) ok_ = false;
		} else {
			sub_[v] = t;
		}
		return ok_;
	}
	bool join(const Substitution* s) {
		return join(*s);
	}
	bool join(const Substitution& s) {
		for (const auto& p : s.sub_) {
			if (!ok_) return false;
			join(p.first, p.second);
		}
		return ok_;
	}
	const map<Symbol, Tree>& sub() const { return sub_; }
	bool ok() const { return ok_; }
	operator bool() const { return ok_; }

private:
	map<Symbol, Tree> sub_;
	bool ok_;
};


Substitution unify_forth(const Tree& p, const Tree& q);
inline Substitution unify_forth(const Expr& ex1, const Expr& ex2) {
	return unify_forth(ex1.tree, ex2.tree);
}
//Expr assemble(const Expr& ex);
//Expr assemble(const Tree* t);

void apply(const Substitution* s, Tree& t);
void apply(const Substitution* s, Expr& e);

Tree apply_(const Substitution*, const Tree&);
Expr apply(const Substitution*, const Expr&);
inline Expr apply(const Substitution& s, const Expr& e) {
	return apply(&s, e);
}

inline void make_non_replaceable(Tree& t) {
	if (t.kind == Tree::VAR)
		t.var()->rep = false;
	else if (t.kind == Tree::NODE)
		for (auto& c : t.children())
			make_non_replaceable(*c.get());
}

inline void make_non_replaceable(Expr& e) {
	for (auto& s : e.symbols)
		s.rep = false;
	make_non_replaceable(e.tree);
}

inline Expr create_non_replaceable(const Expr& e) {
	Expr ex(e);
	make_non_replaceable(ex);
	return ex;
}

namespace expr {
	void enqueue(Expr& ex);
	void parse();
}

string show(const Expr&);
string show_ast(const Tree&, bool full = false);
inline string show_ast(const Expr& ex, bool full = false) {
	return show_ast(ex.tree, full);
}

string show(const Tree& t, bool full = false);


inline string show(const Substitution& s) {
	string str;
	for (const auto& p : s.sub()) {
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
void dump(const Tree* tm);
void dump_ast(const Tree* tm);
void dump(const Substitution& sb);


size_t memvol(const Symbol& s);
size_t memvol(const Tree& t);
size_t memvol(const Expr& ex);
size_t memvol(const Rules&);

}} // mdl::rus

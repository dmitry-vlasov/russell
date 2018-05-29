#pragma once

#include "rus_sys.hpp"

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
	uint literal() const { return lit; }

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
	Symbol(uint l, Id i, Kind k) : Literal(l) {
		set_kind(k);
		if (var) {
			val = unique_ptr<User<Type>>(new User<Type>(i));
		} else if (cst) {
			val = unique_ptr<User<Const>>(new User<Const>(i));
		}
	}
	Symbol(const Symbol& s) : Literal(s) { operator = (s); }
	Symbol(Symbol&& s) : Literal(s) { operator = (std::move(s)); }

	void operator = (const Symbol& s) {
		Literal::operator = (s);
		if (var) {
			val = unique_ptr<User<Type>>(new User<Type>(s.type_id()));
		}
		if (cst) {
			val = unique_ptr<User<Const>>(new User<Const>(lit));
		}
	}
	void operator = (Symbol&& s) {
		Literal::operator = (s);
		val = std::move(s.val);
	}

	uint type_id() const { return var ? std::get<unique_ptr<User<Type>>>(val).get()->id() : UNDEF_UINT; }
	uint constant_id() const { return cst ? std::get<unique_ptr<User<Const>>>(val).get()->id() : UNDEF_UINT; }
	Type* type() { return var ? std::get<unique_ptr<User<Type>>>(val).get()->get() : nullptr; }
	Const* constant() { return cst ? std::get<unique_ptr<User<Const>>>(val).get()->get() : nullptr; }
	const Type* type() const { return var ? std::get<unique_ptr<User<Type>>>(val).get()->get() : nullptr; }
	const Const* constant() const { return cst ? std::get<unique_ptr<User<Const>>>(val).get()->get() : nullptr; }
	void set_type(Id i) { set_type(i.id); }

	void set_type(uint t) {
		if (t == UNDEF_UINT) return;
		val = unique_ptr<User<Type>>(new User<Type>(t));
		var = true;
		rep = true;
	}

	void set_const() {
		if (is_undef()) return;
		val = unique_ptr<User<Const>>(new User<Const>(lit));
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
	typedef variant<unique_ptr<User<Type>>, unique_ptr<User<Const>>> Value;
	Value val;
};

typedef vector<Symbol> Symbols;

string show(Symbol s, bool full = false);

inline ostream& operator << (ostream& os, const Symbol& s) {
	os << Lex::toStr(s.lit); return os;
}

struct Tree {
	typedef vector<unique_ptr<Tree>> Children;
	enum Kind { NODE, VAR };

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

	Tree() = delete;
	Tree(const Symbol& v) : val(unique_ptr<Symbol>(new Symbol(v))) { }
	Tree(Id i, const Children& ch) : val(unique_ptr<Node>(new Node(i, ch))) { }
	Tree(Id i, Tree* ch) : val(unique_ptr<Node>(new Node(i, ch))) { }
	Tree(const Tree& ex) { operator = (ex); }
	Tree(Tree&& ex) { operator = (std::move(ex)); }

	void operator = (Tree&& ex) {
		val = std::move(ex.val);
	}
	void operator = (const Tree& ex) {
		switch (ex.kind()) {
		case NODE: val = unique_ptr<Node>(new Node(*ex.node()));     break;
		case VAR:  val = unique_ptr<Symbol>(new Symbol(*ex.var())); break;
		}
	}
	bool operator == (const Tree& e) const {
		if (kind() != e.kind()) return false;
		switch (kind()) {
		case NODE:
			if (rule() != e.rule()) return false;
			return std::equal(
				children().begin(),children().end(),
				e.children().begin(), e.children().end(),
				[] (auto const& c1, auto const& c2) -> bool { return *c1 == *c2; }
			);
		case VAR: return *var() == *e.var();
		}
		return true;
	}
	bool operator != (const Tree& e) const { return !operator == (e); }
	bool leaf() const { return kind() == VAR || !children().size(); }
	Kind kind() const { return static_cast<Kind>(val.index()); }

	uint rule_id() const { assert(kind() == NODE); return std::get<unique_ptr<Node>>(val).get()->rule.id(); }
	Symbol* var() { assert(kind() == VAR); return std::get<unique_ptr<Symbol>>(val).get(); }
	Node* node() { assert(kind() == NODE); return std::get<unique_ptr<Node>>(val).get(); }
	Rule* rule() { assert(kind() == NODE); return std::get<unique_ptr<Node>>(val).get()->rule.get(); }
	Children& children() { assert(kind() == NODE); return std::get<unique_ptr<Node>>(val).get()->children; }
	Type* type();

	const Symbol* var() const { assert(kind() == VAR); return std::get<unique_ptr<Symbol>>(val).get(); }
	const Node* node() const { assert(kind() == NODE); return std::get<unique_ptr<Node>>(val).get(); }
	const Rule* rule() const { assert(kind() == NODE); return std::get<unique_ptr<Node>>(val).get()->rule.get(); }
	const Children& children() const { assert(kind() == NODE); return std::get<unique_ptr<Node>>(val).get()->children; }
	const Type* type() const;
	uint arity() const {
		switch (kind()) {
		case NODE: return children().size();
		case VAR:  return 0;
		default:   assert(0 && "impossible"); return -1;
		}
	}
	set<uint> vars() const {
		set<uint> ret;
		switch (kind()) {
		case NODE:
			for (const auto& c : node()->children) {
				for (uint v : c.get()->vars()) {
					ret.insert(v);
				}
			}
			break;
		case VAR:  ret.insert(var()->lit); break;
		default:   assert(0 && "impossible"); return set<uint>();
		}
		return ret;
	}

private:
	typedef variant<unique_ptr<Node>, unique_ptr<Symbol>> Value;
	Value val;
};

class Expr;

namespace expr { void parse_LL(Expr*); }

struct Expr : public Tokenable {
	Expr(const Token& t = Token()) : Tokenable(t) { }
	Expr(Symbol s, const Token& t = Token()) : Tokenable(t), type(s.type()) { symbols.push_back(s); }
	Expr(const Symbols& ss, const Token& t = Token()) : Tokenable(t), symbols(ss) { }
	Expr(Id tp, Symbols&& ex, const Token& t = Token()) : Tokenable(t), type(tp), symbols(std::move(ex)) { }
	Expr(Id tp, Symbols&& ex, Tree* tr, const Token& t = Token()) : Tokenable(t), type(tp), tree_(tr), symbols(std::move(ex)) { }
	Expr(const Expr& ex) : Tokenable(ex) { operator = (ex); }
	Expr(Expr&& ex) : Tokenable(ex.token) { operator = (std::move(ex)); }

	void operator = (const Expr& ex) {
		type = ex.type;
		if (ex.tree()) {
			tree_.reset(new Tree(*ex.tree_));
		}
		symbols = ex.symbols;
		token = ex.token;
	}

	void operator = (Expr&& ex) {
		type = ex.type;
		tree_ = std::move(ex.tree_);
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
	Tree* tree() { return tree_.get(); }
	const Tree* tree() const { return tree_.get(); }
	void set(Tree* t) { tree_.reset(t); }

	typedef Symbols::iterator iterator;
	typedef Symbols::const_iterator const_iterator;

	iterator begin() { return symbols.begin(); }
	iterator end() { return symbols.end(); }

	const_iterator begin() const { return symbols.cbegin(); }
	const_iterator end() const { return symbols.cend(); }

	User<Type> type;
	Symbols    symbols;

private:
	unique_ptr<Tree> tree_;
};

struct Rules {
	struct Node;
	typedef vector<unique_ptr<Node>> Nodes;
	typedef Nodes::const_iterator NodeIter;
	typedef map<uint, NodeIter> ConstMap;

	void add(const Expr& ex, uint id);
	void sort();
	vector<string> show() const;
	Rules(Node* p = nullptr) : parent(p) { }
	Node*    parent;
	Nodes    nodes;
	ConstMap constMap;
	NodeIter constLast;
};

struct Rules::Node {
	Node(const Symbol& s, Rules* p) : symb(s), tree(this), parent(p), min_dist(-1) { }
	vector<string> show() const;
	Symbol     symb;
	Rules      tree;
	User<Rule> rule;
	Rules*     parent;
	uint       min_dist;
};


string show(const Rules& tr);

struct Substitution {
	Substitution(bool ok = true) : sub_(), ok_(ok) { }
	Substitution(uint v, const Symbol& t) : sub_(), ok_(true) {
		sub_.emplace(v, t);
	}
	Substitution(uint v, const Tree& t) : sub_(), ok_(true) {
		sub_.emplace(v, t);
	}
	Substitution(const Substitution& s) : sub_(), ok_(s.ok_) {
		operator = (s);
	}
	Substitution(Substitution&& s) : sub_(), ok_(s.ok_) {
		operator = (std::move(s));
	}
	void operator = (const Substitution& s) {
		ok_ = s.ok_;
		if (ok_) for (const auto& p : s.sub_) {
			sub_.emplace(p.first, p.second);
		}
	}
	void operator = (Substitution&& s) {
		ok_ = s.ok_;
		sub_ = std::move(s.sub_);
		s.ok_ = true;
	}
	bool join(uint v, const Symbol& t) {
		return join(v, Tree(t));
	}
	bool join(uint v, const Tree& t) {
		if (!ok_) return false;
		auto it = sub_.find(v);
		if (it != sub_.end()) {
			if ((*it).second != t) ok_ = false;
		} else {
			sub_.emplace(v, t);
		}
		return ok_;
	}
	bool join(uint v, Tree&& t) {
		if (!ok_) return false;
		auto it = sub_.find(v);
		if (it != sub_.end()) {
			if ((*it).second != t) ok_ = false;
		} else {
			sub_.emplace(v, std::move(t));
		}
		return ok_;
	}
	bool join(const Substitution* s) {
		return join(*s);
	}
	bool join(const Substitution& s) {
		if (s.ok_) {
			for (const auto& p : s.sub_) {
				if (!ok_) return false;
				join(p.first, p.second);
			}
		} else {
			ok_ = false;
		}
		return ok_;
	}
	bool join(Substitution&& s) {
		if (s.ok_) {
			for (auto&& p : s.sub_) {
				if (!ok_) return false;
				join(p.first, std::move(p.second));
			}
		} else {
			ok_ = false;
		}
		return ok_;
	}
	const map<uint, Tree>& sub() const { return sub_; }
	bool ok() const { return ok_; }
	operator bool() const { return ok_; }
	bool mapsVar(uint v) const { return sub_.find(v) != sub_.end(); }

private:
	map<uint, Tree> sub_;
	bool ok_;
};


Substitution unify_forth(const Tree* p, const Tree* q);
inline Substitution unify_forth(const Expr& ex1, const Expr& ex2) {
	return unify_forth(ex1.tree(), ex2.tree());
}

void  apply(const Substitution* s, Expr& e);
Tree* apply(const Substitution*, const Tree*);
Expr  apply(const Substitution*, const Expr&);
inline Expr apply(const Substitution& s, const Expr& e) {
	return apply(&s, e);
}

inline void make_non_replaceable(Tree* t) {
	if (t->kind() == Tree::VAR) {
		t->var()->rep = false;
	} else if (t->kind() == Tree::NODE) {
		for (auto& c : t->children()) {
			make_non_replaceable(c.get());
		}
	}
}

inline void make_non_replaceable(Expr& e) {
	for (auto& s : e.symbols) {
		s.rep = false;
	}
	make_non_replaceable(e.tree());
}

inline Expr create_non_replaceable(const Expr& e) {
	Expr ex(e);
	make_non_replaceable(ex);
	return ex;
}

inline void create_rule_term(Expr& ex, Id id) {
	Tree::Children children;
	for (auto& s : ex.symbols) {
		if (s.var) children.push_back(make_unique<Tree>(s));
	}
	ex.set(new Tree(id, children));
}

namespace expr {
	void enqueue(Expr& ex);
	void parse();
}

string show(const Expr&);
string show(const Tree* t, bool full = false);
string show_ast(const Tree*, bool full = false);

inline string show_ast(const Expr& ex, bool full = false) {
	return show_ast(ex.tree(), full);
}

inline string show(const Substitution& s) {
	string str;
	for (const auto& p : s.sub()) {
		str += show(p.first, true) + " --> " + show_ast(&p.second) + "\t ==\t"  + show(&p.second) + "\n";
	}
	return str;
}

inline ostream& operator << (ostream& os, const Expr& ex) {
	for (const auto& s : ex.symbols) {
		os << Lex::toStr(s.lit) << " ";
	}
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

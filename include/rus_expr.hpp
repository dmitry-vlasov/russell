#pragma once

#include "literal.hpp"
#include "rus_sys.hpp"

namespace mdl { namespace rus {

#define END_MARKER ";;"

typedef mdl::Token<Source> Token;
typedef mdl::Tokenable<Source> Tokenable;
typedef mdl::Id<Sys> Id;

struct Type;
struct Rule;

struct Symbol {
	enum Kind { CONST, VAR, NONE };
	Kind kind() const { return kind_; }

	Symbol() : lit(-1), kind_(NONE) { val_.const_ = nullptr; }
	Symbol(uint l) : lit(l), kind_(NONE) { val_.const_ = nullptr; }
	Symbol(uint l, Id i, Kind k) : lit(l), kind_(k) {
		if (i.id() != -1) {
			switch (kind_) {
			case VAR:   val_.type_ = new User<Type>(i); break;
			case CONST: val_.const_ = new User<Const>(i); break;
			default: break;
			}
		}
	}
	Symbol(const Symbol& s) : lit(s.lit), kind_(NONE) { operator = (s); }
	Symbol(Symbol&& s) : lit(s.lit), kind_(NONE) { operator = (std::move(s)); }
	~Symbol() { clear(); }

	bool operator == (const Symbol& s) const { return lit == s.lit; }
	bool operator != (const Symbol& s) const { return !operator ==(s); }
	bool operator < (const Symbol& s) const { return lit < s.lit; }
	bool is_undef() const { return lit == -1; }

	void operator = (const Symbol& s) {
		clear();
		lit = s.lit;
		kind_ = s.kind_;
		switch (kind_) {
		case VAR:   val_.type_ = new User<Type>(s.type_id()); break;
		case CONST: val_.const_ = new User<Const>(s.constant_id()); break;
		default:    break;
		}
	}
	void operator = (Symbol&& s) {
		clear();
		lit = s.lit;
		kind_ = s.kind_;
		if (kind_ != NONE) {
			val_ = s.val_;
			s.val_.const_ = nullptr;
			s.kind_ = NONE;
		}
	}

	uint type_id() const { return kind_ == VAR ? val_.type_->id() : -1; }
	uint constant_id() const { return kind_ == CONST ? val_.type_->id() : -1; }
	Type* type() { return kind_ == VAR ? val_.type_->get() : nullptr; }
	Const* constant() { return kind_ == CONST ? val_.const_->get() : nullptr; }
	const Type* type() const { return kind_ == VAR ? val_.type_->get() : nullptr; }
	const Const* constant() const { return kind_ == CONST ? val_.const_->get() : nullptr; }
	const Token* token() const {
		switch (kind_) {
		case VAR:   return &val_.type_->token;
		case CONST: return &val_.const_->token;
		default:    return nullptr;
		}
	}
	const Tokenable* tokenable() const;
	void set_type(Id i) { set_type(i.id()); }
	void set_type(uint t) {
		clear();
		kind_ = VAR;
		val_.type_ = new User<Type>(t);
	}
	void set_const() {
		clear();
		kind_ = CONST;
		val_.const_ = new User<Const>(lit);
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

	uint lit;

private:
	void clear() {
		switch (kind_) {
		case CONST: delete val_.const_; break;
		case VAR:   delete val_.type_; break;
		default:    break;
		}
		kind_ = NONE;
		val_.const_ = nullptr;
	}
	union Value {
		User<Const>* const_;
		User<Type>*  type_;
	};
	Kind kind_;
	Value val_;
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

		CompactUser<Rule> rule;
		Children children;
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
	Symbol* var() { return kind() == VAR ? std::get<unique_ptr<Symbol>>(val).get() : nullptr; }
	Node* node() { return kind() == NODE ? std::get<unique_ptr<Node>>(val).get() : nullptr; }
	Rule* rule() { return  kind() == NODE ? std::get<unique_ptr<Node>>(val).get()->rule.get() : nullptr; }
	Children& children() { assert(kind() == NODE); return std::get<unique_ptr<Node>>(val).get()->children; }
	Type* type();

	const Symbol* var() const { return kind() == VAR ? std::get<unique_ptr<Symbol>>(val).get() : nullptr; }
	const Node* node() const { return kind() == NODE ? std::get<unique_ptr<Node>>(val).get() : nullptr; }
	const Rule* rule() const { return  kind() == NODE ? std::get<unique_ptr<Node>>(val).get()->rule.get() : nullptr; }
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
				for (uint v : c->vars()) {
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
	bool operator == (const Expr& ex) const {
		return (type == ex.type) && (symbols == ex.symbols);
	}
	bool operator != (const Expr& ex) const {
		return !operator == (ex);
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
	Node(const Symbol& s, Rules* p) : symb(s), tree(this), parent(p), min_dist(-1), final(false) { }
	vector<string> show() const;
	Symbol     symb;
	Rules      tree;
	User<Rule> rule;
	Rules*     parent;
	uint       min_dist;
	bool       final;
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

	void operator = (const Substitution& s);
	void operator = (Substitution&& s);
	bool join(uint v, const Symbol& t) {
		return join(v, Tree(t));
	}
	bool join(uint v, const Tree& t);
	bool join(uint v, Tree&& t);
	bool join(const Substitution* s) {
		return join(*s);
	}
	bool join(const Substitution& s);
	bool join(Substitution&& s);

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

inline void create_rule_term(Expr& ex, Id id) {
	Tree::Children children;
	for (auto& s : ex.symbols) {
		if (s.kind() == Symbol::VAR) {
			children.push_back(make_unique<Tree>(s));
		}
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

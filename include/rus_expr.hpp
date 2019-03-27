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

struct Symbol : Writable {
	enum Kind { CONST, VAR, LITERAL };
	virtual ~Symbol() { }

	virtual uint lit() const = 0;
	virtual Kind kind() const = 0;
	virtual Symbol* clone() const = 0;

	virtual const Type* type() const { return nullptr; }
	virtual const Token* token() const { return nullptr; }
	virtual const Tokenable* tokenable() const { return nullptr; }
	virtual string showDetailed() const { return Lex::toStr(lit()); }

	bool operator == (const Symbol& s) const { return lit() == s.lit(); }
	bool operator != (const Symbol& s) const { return !operator ==(s); }
	bool operator < (const Symbol& s) const { return lit() < s.lit(); }
	void write(ostream& os, const Indent& indent = Indent()) const override {
		os << indent << Lex::toStr(lit());
	}

	struct Hash {
		typedef size_t result_type;
		typedef Symbol argument_type;
		size_t operator() (const Symbol& s) const {
			return hash(s.lit());
		}
	private:
		static std::hash<uint> hash;
	};
};

struct Literal : public Symbol {
	Literal(uint l) : lit_(l) { }
	Literal(const Literal& c) = default;
	Literal(Literal&& c) = default;
	Literal& operator = (const Literal& s) = default;
	Literal& operator = (Literal&& s) = default;

	Kind kind() const override { return LITERAL; }
	uint lit() const override { return lit_; }
	Symbol* clone() const override { return new Literal(*this); }
	string showDetailed() const override { return "[" + Lex::toStr(lit()) + "]"; }

private:
	uint lit_;
};

struct Const : public Symbol {
	Const(uint l) : const_(l) { }
	Const(const Const& c) = default;
	Const(Const&& c) = default;
	Const& operator = (const Const& s) = default;
	Const& operator = (Const&& s) = default;

	Kind kind() const override { return CONST; }
	uint lit() const override { return const_.id(); }
	Symbol* clone() const override { return new Const(*this); }

	const Constant* constant() const { return const_.get(); }

	const Token* token() const override { return &const_.token; }
	const Tokenable* tokenable() const override;

private:
	User<Constant> const_;
};

struct Var : public Symbol {
	Var(uint l, uint t) : lit_(l), type_(t) { }
	Var(const Var& c) = default;
	Var(Var&& c) = default;
	Var& operator = (const Var& s) = default;
	Var& operator = (Var&& s) = default;

	Kind kind() const override { return VAR; }
	uint lit() const override { return lit_; }
	uint typeId() const { return type_.id(); }
	Symbol* clone() const override { return new Var(*this); }
	const Type* type() const override { return type_.get(); }
	string showDetailed() const override {
		return Lex::toStr(lit()) + " <" + Lex::toStr(type_.id()) + ">";
	}

	const Token* token() const override { return &type_.token; }
	const Tokenable* tokenable() const override;

private:
	uint lit_;
	User<Type> type_;
};

typedef vector<unique_ptr<Symbol>> Symbols;

struct Tree : public Writable{
	typedef vector<unique_ptr<Tree>> Children;

	enum Kind { RULE, VAR };

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
	Tree(const Var& v) : val(v) { }
	Tree(Id i, const Children& ch) : val(std::move(Node(i, ch))) { }
	Tree(Id i, Tree* ch) : val(std::move(Node(i, ch))) { }
	Tree(const Tree& ex) = default;
	Tree(Tree&& ex) = default;
	Tree& operator = (Tree&& ex) = default;
	Tree& operator = (const Tree& ex) = default;

	bool operator == (const Tree& e) const {
		if (kind() != e.kind()) return false;
		switch (kind()) {
		case RULE:
			if (rule() != e.rule()) return false;
			return std::equal(
				children().begin(),children().end(),
				e.children().begin(), e.children().end(),
				[] (auto const& c1, auto const& c2) -> bool { return *c1 == *c2; }
			);
		case VAR: return var() == e.var();
		}
		return true;
	}
	bool operator != (const Tree& e) const { return !operator == (e); }
	bool leaf() const { return kind() == VAR || !children().size(); }
	Kind kind() const { return static_cast<Kind>(val.index()); }

	uint rule_id() const { assert(kind() == RULE); return std::get<Node>(val).rule.id(); }
	Var& var() { assert(kind() == VAR); return  std::get<Var>(val); }
	Node& node() { assert(kind() == RULE); return std::get<Node>(val); }
	//Rule* rule() { assert(kind() == RULE); return std::get<Node>(val).rule.get(); }
	Children& children() { assert(kind() == RULE); return std::get<Node>(val).children; }

	const Var& var() const { assert(kind() == VAR); return std::get<Var>(val); }
	const Node& node() const { assert(kind() == RULE); return std::get<Node>(val); }
	const Rule* rule() const { assert(kind() == RULE); return std::get<Node>(val).rule.get(); }
	const Children& children() const { assert(kind() == RULE); return std::get<Node>(val).children; }
	const Type* type() const;
	uint arity() const {
		switch (kind()) {
		case RULE: return children().size();
		case VAR:  return 0;
		default:   assert(0 && "impossible"); return -1;
		}
	}
	set<uint> vars() const {
		set<uint> ret;
		switch (kind()) {
		case RULE:
			for (const auto& c : children()) {
				for (uint v : c->vars()) {
					ret.insert(v);
				}
			}
			break;
		case VAR:  ret.insert(var().lit()); break;
		default:   assert(0 && "impossible"); return set<uint>();
		}
		return ret;
	}
	void write(ostream& os, const Indent& indent = Indent()) const override;

private:
	typedef variant<Node, Var> Value;
	Value val;
};

struct Expr : public Tokenable, public Writable {
	Expr(const Token& t = Token()) : Tokenable(t) { }
	//Expr(const Symbol& s, const Token& t = Token()) :
	//	Tokenable(t), type(s.kind() == Symbol::VAR ? dynamic_cast<const Var&>(s).type() : nullptr) { symbols.emplace_back(s.clone()); }
	//Expr(const Symbols& ss, const Token& t = Token()) :
	//	Tokenable(t), symbols(ss) { }
	Expr(Id tp, Symbols&& ex, const Token& t = Token()) :
		Tokenable(t), type(tp), symbols(std::move(ex)) { }
	Expr(Id tp, Symbols&& ex, Tree* tr, const Token& t = Token()) :
		Tokenable(t), type(tp), tree_(tr), symbols(std::move(ex)) { }
	Expr(const Expr& ex) : Tokenable(ex) { operator = (ex); }
	Expr(Expr&& ex) : Tokenable(ex.token) { operator = (std::move(ex)); }

	void operator = (const Expr& ex) {
		type = ex.type;
		if (ex.tree()) {
			tree_.reset(new Tree(*ex.tree_));
		}
		for (const auto& s : ex.symbols) {
			symbols.emplace_back(s->clone());
		}
		token = ex.token;
	}

	void operator = (Expr&& ex) {
		type = ex.type;
		tree_ = std::move(ex.tree_);
		symbols = std::move(ex.symbols);
		token = ex.token;
	}
	bool operator == (const Expr& ex) const {
		if (symbols.size() != ex.symbols.size()) {
			return false;
		}
		for (uint i = 0; i < symbols.size(); ++ i) {
			if (*symbols[i] != *ex.symbols[i]) {
				return false;
			}
		}
		return (type == ex.type);
	}
	bool operator != (const Expr& ex) const {
		return !operator == (ex);
	}

	void write(ostream& os, const Indent& indent = Indent()) const override {
		if (symbols.size()) {
			os << indent;
			os << *symbols.at(0);
			for (uint i = 1; i < symbols.size(); ++ i) {
				os << " " << *symbols.at(i);
			}
		}
	}
	string showDetailed() const {
		string ret;
		if (symbols.size()) {
			ret +=  symbols.at(0)->showDetailed();
			for (uint i = 1; i < symbols.size(); ++ i) {
				ret += " " + symbols.at(i)->showDetailed();
			}
		}
		return ret;
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
	Symbols symbols;

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
	Node(const Symbol& s, Rules* p) :
		symb(s.clone()), tree(this), parent(p), min_dist(-1), final(false) { }
	vector<string> show() const;
	unique_ptr<Symbol> symb;
	Rules      tree;
	User<Rule> rule;
	Rules*     parent;
	uint       min_dist;
	bool       final;
};


string show(const Rules& tr);

struct Substitution : public Writable {
	Substitution(bool ok = true) : sub_(), ok_(ok) { }
	/*Substitution(uint v, const Symbol& t) : sub_(), ok_(true) {
		sub_.emplace(v, t);
	}*/
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
	/*bool join(uint v, const Symbol& t) {
		return join(v, Tree(t));
	}*/
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

	void write(ostream& os, const Indent& indent = Indent()) const override {
		for (const auto p : sub_) {
			os << indent << Lex::toStr(p.first) << " --> " << static_cast<const Writable&>(p.second) << endl;
		}
	}

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
		if (const Var* v = dynamic_cast<const Var*>(s.get())) {
			children.push_back(make_unique<Tree>(*v));
		}
	}
	ex.set(new Tree(id, children));
}

namespace expr {
	void enqueue(Expr& ex);
	void parse();
}

size_t memvol(const Symbol& s);
size_t memvol(const Tree& t);
size_t memvol(const Expr& ex);
size_t memvol(const Rules&);

}} // mdl::rus

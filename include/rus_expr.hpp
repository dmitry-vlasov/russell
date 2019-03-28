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

struct Tree : public Writable {
	enum Kind { RULE, VAR };
	virtual ~Tree() { }

	virtual Kind kind() const = 0;
	virtual const Type* type() const = 0;
	virtual set<uint> vars() const = 0;
	virtual uint arity() const = 0;
	virtual Tree* clone() const = 0;

	bool operator == (const Tree&) const;
	bool operator != (const Tree& t) const { return !operator ==(t); }

	bool leaf() const { return arity() == 0; }
};

struct RuleTree : public Tree {
	typedef vector<unique_ptr<Tree>> Children;

	RuleTree(Id = Id());
	RuleTree(const RuleTree& n);
	RuleTree(RuleTree&& n);
	RuleTree(Id i, const Children& ch);
	RuleTree(Id i, Children&& ch);
	RuleTree(Id i, Tree* ch);

	Kind kind() const override { return RULE; }
	const Type* type() const override;
	set<uint> vars() const override {
		set<uint> ret;
		for (const auto& c : children) {
			for (uint v : c->vars()) {
				ret.insert(v);
			}
		}
		return ret;
	}
	uint arity() const override { return children.size(); }
	Tree* clone() const override { return new RuleTree(*this); }
	void write(ostream& os, const Indent& indent = Indent()) const override;

	CompactUser<Rule> rule;
	Children children;
};

struct VarTree : public Tree {
	VarTree(const Var& v) : var(v) { }
	VarTree(const VarTree& n) = default;
	VarTree(VarTree&& n) = default;

	Kind kind() const override { return VAR; }
	const Type* type() const override;
	set<uint> vars() const override {
		set<uint> ret;
		ret.insert(var.lit());
		return ret;
	}
	uint arity() const override { return 0; }
	Tree* clone() const override { return new VarTree(*this); }
	void write(ostream& os, const Indent& indent = Indent()) const override;

	Var var;
};

struct Expr : public Tokenable, public Writable {
	Expr(const Token& t = Token()) : Tokenable(t) { }
	Expr(Id tp, Symbols&& ex, const Token& t = Token()) :
		Tokenable(t), type(tp), symbols(std::move(ex)) { }
	Expr(Id tp, Symbols&& ex, Tree* tr, const Token& t = Token()) :
		Tokenable(t), type(tp), tree_(tr), symbols(std::move(ex)) { }
	Expr(const Expr& ex) : Tokenable(ex) { operator = (ex); }
	Expr(Expr&& ex) : Tokenable(ex.token) { operator = (std::move(ex)); }

	void operator = (const Expr& ex) {
		type = ex.type;
		if (ex.tree()) {
			tree_.reset(ex.tree_->clone());
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
	Substitution(uint v, const Tree& t) : sub_(), ok_(true) {
		sub_.emplace(v, t.clone());
	}
	Substitution(const Substitution& s) : sub_(), ok_(s.ok_) {
		operator = (s);
	}
	Substitution(Substitution&& s) : sub_(), ok_(s.ok_) {
		operator = (std::move(s));
	}

	void operator = (const Substitution& s);
	void operator = (Substitution&& s);
	bool join(uint v, unique_ptr<Tree>&& t);
	bool join(uint v, const Tree& t);
	bool join(const Substitution* s) {
		return join(*s);
	}
	bool join(const Substitution& s);
	bool join(Substitution&& s);

	bool maps(uint v) const { return sub_.find(v) != sub_.end(); }
	const Tree* map(uint v) const {
		auto it = sub_.find(v);
		if (sub_.find(v) != sub_.end()) {
			return it->second.get();
		} else {
			return nullptr;
		}
	}
	void erase(uint v) { sub_.erase(v); }

	typedef std::map<uint, unique_ptr<Tree>>::const_iterator const_iterator;

	const_iterator begin() const { return sub_.cbegin(); }
	const_iterator end() const { return sub_.cend(); }

	uint size() const { return sub_.size(); }

	bool ok() const { return ok_; }
	operator bool() const { return ok_; }

	void write(ostream& os, const Indent& indent = Indent()) const override {
		for (const auto& p : sub_) {
			os << indent << Lex::toStr(p.first) << " --> " << static_cast<const Writable&>(*p.second) << endl;
		}
	}

private:
	std::map<uint, unique_ptr<Tree>> sub_;
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
	RuleTree::Children children;
	for (auto& s : ex.symbols) {
		if (const Var* v = dynamic_cast<const Var*>(s.get())) {
			children.push_back(make_unique<VarTree>(*v));
		}
	}
	ex.set(new RuleTree(id, children));
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

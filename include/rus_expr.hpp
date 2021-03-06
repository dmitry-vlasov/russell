#pragma once

#include "literal.hpp"
#include "rus_sys.hpp"

namespace mdl { namespace rus {

#define END_MARKER ";;"

typedef mdl::Token<Source> Token;
typedef mdl::WithToken<Source> WithToken;
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

struct Const : public Symbol, public WithToken {
	Const(uint l, const Token& t = Token()) : WithToken(t), const_(l) { }
	Const(const Const& c) = default;
	Const(Const&& c) = default;
	Const& operator = (const Const& s) = default;
	Const& operator = (Const&& s) = default;

	Kind kind() const override { return CONST; }
	uint lit() const override { return const_.id(); }
	Symbol* clone() const override { return new Const(*this); }

	const Constant* constant() const { return const_.get(); }

private:
	User<Constant> const_;
};

struct Var : public Symbol, public WithToken {
	Var(uint l, uint tp, const Token& tk = Token()) : WithToken(tk), lit_(l), type_(tp) { }
	Var(uint l, const Type* tp, const Token& tk = Token()) : WithToken(tk), lit_(l), type_(tp) { }
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
	virtual uint len() const = 0;
	virtual void traverse(std::function<void (Tree&)> f) = 0;
	virtual void traverse(std::function<void (const Tree&)> f) const = 0;

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
	uint len() const override {
		uint l = 1;
		for (const auto& c : children) {
			l += c->len();
		}
		return l;
	}
	void write(ostream& os, const Indent& indent = Indent()) const override;
	void traverse(std::function<void (Tree&)> f) override {
		f(*this); for (auto& c : children) if (c) c->traverse(f);
	}
	void traverse(std::function<void (const Tree&)> f) const override {
		f(*this); for (auto& c : children) if (c) const_cast<const Tree*>(c.get())->traverse(f);
	}

	User<Rule> rule;
	Children children;
};

struct VarTree : public Tree {
	VarTree(uint l, const Type* t) : lit_(l), type_(t) { }
	VarTree(const Var& v) : lit_(v.lit()), type_(v.typeId()) { }
	VarTree(const VarTree& n) = default;
	VarTree(VarTree&& n) = default;

	Kind kind() const override { return VAR; }
	const Type* type() const override;
	set<uint> vars() const override {
		set<uint> ret;
		ret.insert(lit_);
		return ret;
	}
	uint arity() const override { return 0; }
	Tree* clone() const override { return new VarTree(*this); }
	uint len() const override { return 1; }
	void write(ostream& os, const Indent& indent = Indent()) const override;
	uint lit() const { return lit_; }
	Var var() const { return Var(lit_, type_.get()); }
	void traverse(std::function<void (Tree&)> f) override { f(*this); }
	void traverse(std::function<void (const Tree&)> f) const override { f(*this); }

private:
	uint lit_;
	User<Type> type_;
};

struct Expr : public Writable, public WithToken {
	Expr(const Token& t = Token()) : WithToken(t) { }
	Expr(Id tp, Symbols&& ex, const Token& t = Token()) :
		WithToken(t), type(tp), symbols(std::move(ex)) { }
	Expr(Id tp, Symbols&& ex, Tree* tr, const Token& t = Token()) :
		WithToken(t), type(tp), tree_(tr), symbols(std::move(ex)) { }
	Expr(const Expr& ex) : WithToken(ex) { operator = (ex); }
	Expr(Expr&& ex) : WithToken(ex) { operator = (std::move(ex)); }

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
			for (uint i = 0; i < symbols.size(); ++ i) {
				os << *symbols.at(i) << " ";
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
	vector<const Var*> vars() const {
		vector<const Var*> ret;
		for (auto& s : symbols) {
			if (const Var* v = dynamic_cast<const Var*>(s.get())) {
				ret.push_back(v);
			}
		}
		return ret;
	}
	void rebuildSymbols();

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
	Substitution(bool ok = true) : ok_(ok) { }
	Substitution(const Var& v, const Tree& t) : sub_(), ok_(true) {
		join(v, t);
	}
	Substitution(uint v, const Type* tp,  const Tree& tr) : sub_(), ok_(true) {
		join(v, tp, tr);
	}
	Substitution(const Substitution& s) : ok_(s.ok_) {
		operator = (s);
	}
	Substitution(Substitution&& s) : sub_(), ok_(s.ok_) {
		operator = (std::move(s));
	}

	void operator = (const Substitution& s);
	void operator = (Substitution&& s);
	bool join(const Var& v, unique_ptr<Tree>&& t);
	bool join(const Var& v, const Tree& t);
	bool join(uint v, const Type* tp, const Tree& tr);
	bool join(uint v, const Type* tp, unique_ptr<Tree>&& tr);
	bool join(const Substitution* s) {
		return join(*s);
	}
	bool join(const Substitution& s);
	bool join(Substitution&& s);

	bool joinable(const Var& v, const Tree& t) const;
	bool joinable(uint v, const Type* tp, const Tree& tr) const;
	bool joinable(const Substitution* s) const {
		return joinable(*s);
	}
	bool joinable(const Substitution& s) const;

	bool maps(uint v) const { return sub_.find(v) != sub_.end(); }
	const Tree* map(uint v) const {
		auto it = sub_.find(v);
		if (sub_.find(v) != sub_.end()) {
			return it->second.tree.get();
		} else {
			return nullptr;
		}
	}
	//void erase(const Var& v) { sub_.erase(v); }

	struct TypeTree {
		TypeTree(const Var& v, const Tree& t) : type(v.type()), tree(t.clone()) { }
		TypeTree(const Type* tp, const Tree& tr) : type(tp), tree(tr.clone()) { }
		TypeTree(const Type* tp, unique_ptr<Tree>&& tr) : type(tp), tree(std::move(tr)) { }
		TypeTree(TypeTree&&) = default;
		TypeTree(const TypeTree& tt) : type(tt.type), tree(tt.tree->clone()) { }
		User<Type> type;
		unique_ptr<Tree> tree;
	};
	typedef hmap<uint, TypeTree> Sub_;
	typedef Sub_::const_iterator const_iterator;

	const_iterator begin() const { return sub_.cbegin(); }
	const_iterator end() const { return sub_.cend(); }

	uint size() const { return sub_.size(); }

	bool ok() const { return ok_; }
	operator bool() const { return ok_; }
	void spoil() { ok_ = false; }

	void write(ostream& os, const Indent& indent = Indent()) const override {
		for (const auto& p : sub_) {
			os << indent << Lex::toStr(p.first) << " --> " << static_cast<const Writable&>(*p.second.tree) << endl;
		}
	}

private:
	Sub_ sub_;
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

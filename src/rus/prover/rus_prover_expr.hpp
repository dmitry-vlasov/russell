#pragma once

#include <rus_expr.hpp>
#include <rus_ast.hpp>

namespace mdl { namespace rus { namespace prover {

enum class ReplMode {
	KEEP_REPL,
	DENY_REPL
};

constexpr uint undefined_value = uint(-1) >> 1;
constexpr uint lambda_value = undefined_value - 1;

struct LightSymbol {
	enum {
		MATH_INDEX = 0,
		ASSERTION_INDEX = 1,
		INTERNAL_MIN_INDEX = 2
	};
	LightSymbol() : lit(undefined_value), rep(false), ind(-1), type(nullptr)  { }
	LightSymbol(const rus::Symbol& s, ReplMode mode, uint i) :
		lit(i == MATH_INDEX ? s.lit :
			(i == ASSERTION_INDEX ? Lex::toInt(Lex::toStr(s.lit) + "!") :
				Lex::toInt(Lex::toStr(s.lit) + "_" + to_string(i - LightSymbol::INTERNAL_MIN_INDEX))
			)
		),
		rep(s.kind() == Symbol::VAR),
		ind(i),
		type(s.kind() == Symbol::VAR ? s.type() : nullptr) {
		if (mode == ReplMode::DENY_REPL) {
			rep = false;
		}
	}
	LightSymbol(const LightSymbol& s) = default;
	static LightSymbol lambda() { LightSymbol ret; ret.lit = lambda_value; return ret; }

	bool is_undef() const { return lit == undefined_value; }
	bool is_def() const { return lit != undefined_value; }
	bool is_lambda() const { return lit == lambda_value; }
	uint literal() const { return lit; }

	bool operator == (const LightSymbol& s) const { return lit == s.lit && ind == s.ind; }
	bool operator != (const LightSymbol& s) const { return !operator ==(s); }
	bool operator < (const LightSymbol& s) const {
		if (lit < s.lit) return true;
		else if (lit > s.lit) return false;
		else return ind < s.ind;
	}

	LightSymbol& operator = (const LightSymbol& s) = default;

	uint lit:31;
	bool rep:1;
	uint ind;
	const Type* type;
};

struct LightTree {
	typedef vector<unique_ptr<LightTree>> Children;
	enum Kind { RULE, VAR };

	struct Node {
		Node() = delete;
		Node(const Node& n) : rule_(n.rule_) {
			for (auto& c : n.children_) {
				if (!c.get()) {
					throw Error("!c.get()");
				}
				children_.push_back(make_unique<LightTree>(*c.get()));
			}
		}
		Node(Node&& n) : rule_(n.rule_), children_(std::move(n.children_)) { }
		Node(const Rule* r, const Children& ch) : rule_(r) {
			children_.reserve(ch.size());
			for (auto& c : ch) {
				if (!c.get()) {
					throw Error("!c.get()");
				}
				children_.push_back(make_unique<LightTree>(*c.get()));
			}
		}
		Node(const Rule* r, Children&& ch) : rule_(r), children_(std::move(ch)) { }
		Node(const Rule* r, LightTree* ch) : rule_(r) {
			children_.emplace_back(ch);
		}
		void operator = (const Node& n) {
			rule_ = n.rule_;
			for (auto& c : n.children_) {
				children_.push_back(make_unique<LightTree>(*c.get()));
			}
		}
		void operator = (Node&& n) {
			rule_ = n.rule_;
			children_ = std::move(n.children_);
		}
		const Rule* rule() const { return rule_; }
		const Children& children() const { return children_; }
	private:
		const Rule* rule_;
		Children children_;
	};

	LightTree() : val(LightSymbol()) { }
	LightTree(const LightSymbol& v) : val(LightSymbol(v)) { }
	LightTree(const Rule* r, const Children& ch = Children()) : val(Node(r, ch)) { }
	LightTree(const Rule* r, LightTree* ch) : val(Node(r, ch)) { }
	LightTree(const LightTree& ex) = default;
	LightTree(LightTree&& ex) = default;

	void operator = (const LightTree& e) {
		switch (e.kind()) {
		case RULE: val = Node(e.rule(), e.children()); break;
		case VAR:  val = LightSymbol(e.var());         break;
		default: assert(false && "impossible");        break;
		}
	}
	void operator = (LightTree&& e) {
		switch (e.kind()) {
		case RULE: val = Node(e.rule(), std::move(e.children())); break;
		case VAR:  val = LightSymbol(e.var());         break;
		default: assert(false && "impossible");        break;
		}
	}

	bool operator == (const LightTree& e) const {
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
	bool operator != (const LightTree& e) const { return !operator == (e); }
	bool leaf() const { return kind() == VAR || !children().size(); }
	Kind kind() const { return static_cast<Kind>(val.index()); }
	bool empty() const { return kind() == VAR && var().is_undef(); }

	LightSymbol var() const {
		assert(kind() == VAR);
		return std::get<LightSymbol>(val);
	}
	const Rule* rule() const {
		assert(kind() == RULE);
		return std::get<Node>(val).rule();
	}
	const Type* type() const {
		return kind() == VAR ? var().type : rule()->term.type.get();
	}
	const Children& children() const {
		assert(kind() == RULE);
		return std::get<Node>(val).children();
	}

	uint arity() const {
		switch (kind()) {
		case RULE: return std::get<Node>(val).children().size();
		case VAR:  return 0;
		default:   assert(0 && "impossible"); return -1;
		}
	}
	uint length() const {
		switch (kind()) {
		case RULE: {
			uint len = 0;
			uint i = 0;
			for (const auto& s : rule()->term.symbols) {
				if (s.type()) {
					len += children()[i++].get()->length();
				} else {
					len += 1;
				}
			}
			return len;
		}
		case VAR:  return 1;
		default:   assert(0 && "impossible"); return -1;
		}
	}
	uint len() const {
		uint len = 1;
		if (kind() == RULE) {
			for (const auto& c : children()) {
				len += c->len();
			}
		}
		return len;
	}

private:
	typedef variant<Node, LightSymbol> Value;
	Value val;
};

struct Subst {
	Subst(bool ok = true) : ok_(ok) { }
	Subst(LightSymbol v, const LightTree& t) : ok_(true) {
		if (!(t.kind() == LightTree::VAR && t.var() == v)) {
			sub_.emplace(v, t);
		}
	}
	Subst(const Subst& s) : ok_(s.ok_) {
		operator = (s);
	}
	Subst(Subst&& s) : ok_(s.ok_) {
		operator = (std::move(s));
	}
	void operator = (const Subst& s);
	void operator = (Subst&& s);

	bool operator == (const Subst& s) const;
	bool operator != (const Subst& s) const;

	bool consistent(const Subst& s) const;
	bool compose(const Subst& s, bool full = true);
	bool compose(LightSymbol v, const LightTree& t, bool full = true) { return compose(Subst(v, t), full); }
	bool bicompose(const Subst& s);
	bool intersects(const Subst& s) const;
	bool composeable(const Subst& s) const;

	bool maps(LightSymbol v) const { return sub_.find(v) != sub_.end(); }
	const LightTree& map(LightSymbol v) const {
		auto it = sub_.find(v);
		if (sub_.find(v) != sub_.end()) {
			return it->second;
		} else {
			static LightTree empty; return empty;
		}
	}
	void erase(LightSymbol v) { sub_.erase(v); }

	typedef std::map<LightSymbol, LightTree>::const_iterator const_iterator;

	const_iterator begin() const { return sub_.cbegin(); }
	const_iterator end() const { return sub_.cend(); }

	uint size() const { return sub_.size(); }
	bool ok() const { return ok_; }
	void spoil() { ok_ = false; }

private:
	std::map<LightSymbol, LightTree> sub_;
	bool ok_;
	friend void compose(Subst& s1, const Subst& s2, bool full);
};

void compose(Subst& s1, const Subst& s2, bool full = true);
bool composable(const Subst& s1, const Subst& s2);

unique_ptr<rus::Tree> convert_tree_ptr(const LightTree&);
unique_ptr<LightTree> convert_tree_ptr(const rus::Tree&, ReplMode, uint i);
unique_ptr<LightTree> apply_ptr(const Subst&, const LightTree&);

inline rus::Tree convert_tree(const LightTree& t) {
	return rus::Tree(std::move(*convert_tree_ptr(t).get()));
}
inline LightTree convert_tree(const rus::Tree& t, ReplMode m, uint i) {
	return LightTree(std::move(*convert_tree_ptr(t, m, i).get()));
}
inline LightTree apply(const Subst& s, const LightTree& t) {
	return LightTree(std::move(*apply_ptr(s, t).get()));
}

rus::Expr convert_expr(const LightTree&);
rus::Substitution convert_sub(const Subst&);

string show(const set<uint>&);
string show(const vector<uint>&);
string show(const vector<bool>& v);
string show(const vector<LightSymbol>& v);
string show(LightSymbol s, bool full = true);
string show(const LightTree&, bool full = true);
string show_ast(const LightTree&);
string show(const Subst& s);
string show_diff(const Subst& s1, const Subst& s2);

inline ostream& operator << (ostream& os, const LightSymbol& s) {
	os << show(s); return os;
}

struct MultySubst {
	MultySubst(const vector<const Subst*>& subs);
	Subst makeSubs(Subst& unif) const;

	string show() const {
		ostringstream ret;
		ret << "MultySubst" << endl;
		ret << "==========" << endl;
		uint c = 0;
		for (const auto& p : msub_) {
			ret << c++ << " VAR: " << prover::show(p.first) << endl;
			ret << "TREES:" << endl;
			for (const auto& tree : p.second) {
				ret << Indent::paragraph(prover::show(tree)) << endl;
			}
		}
		return ret.str();
	}

private:
	void add(const Subst* s);
	map<LightSymbol, vector<LightTree>> msub_;
};

extern bool debug_unify_subs_func;
extern bool debug_compose;

void sub_closure(Subst& sub);
Subst unify_subs(Subst unif, Subst gen);
Subst unify_subs(const MultySubst& t);

// Substitutions, which differ only by varaible replacement
bool similar_subs(const Subst& s1, const Subst& s2);

typedef map<vector<uint>, Subst> MultyUnifiedSubs;

}}}

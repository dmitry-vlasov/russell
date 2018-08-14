#pragma once

#include <rus_expr.hpp>
#include <rus_ast.hpp>

namespace mdl { namespace rus { namespace prover {

enum class ReplMode {
	KEEP_REPL,
	DENY_REPL
};

struct LightSymbol {
	enum {
		MATH_INDEX = 0,
		ASSERTION_INDEX = 1,
		INTERNAL_MIN_INDEX = 2
	};
	LightSymbol() : lit(undef()), rep(false), ind(-1), type(nullptr)  { }
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

	bool is_undef() const { return lit == undef(); }
	bool is_def() const { return lit != undef(); }
	static uint undef() { return 0x7FFFFFFF; }
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
	enum Kind { NODE, VAR };

	struct Node {
		Node() = delete;
		Node(const Node& n) : rule(n.rule) {
			for (auto& c : n.children) {
				children.push_back(make_unique<LightTree>(*c.get()));
			}
		}
		Node(Node&& n) : rule(n.rule), children(std::move(n.children)) { }
		Node(const Rule* r, const Children& ch) : rule(r) {
			children.reserve(ch.size());
			for (auto& c : ch) {
				children.push_back(make_unique<LightTree>(*c.get()));
			}
		}
		Node(const Rule* r, Children&& ch) : rule(r), children(std::move(ch)) { }
		Node(const Rule* r, LightTree* ch) : rule(r) {
			children.emplace_back(ch);
		}
		void operator = (const Node& n) {
			rule = n.rule;
			for (auto& c : n.children) {
				children.push_back(make_unique<LightTree>(*c.get()));
			}
		}
		void operator = (Node&& n) {
			rule = n.rule;
			children = std::move(n.children);
		}
		const Rule* rule;
		Children    children;
	};

	LightTree() : val(LightSymbol()) { }
	LightTree(const LightSymbol& v) : val(LightSymbol(v)) { }
	LightTree(const Rule* r, const Children& ch) : val(Node(r, ch)) { }
	LightTree(const Rule* r, LightTree* ch) : val(Node(r, ch)) { }
	LightTree(const LightTree& ex) = default;
	LightTree(LightTree&& ex) = default;

	void operator = (const LightTree& e) {
		switch (e.kind()) {
		case NODE: val = Node(e.rule(), e.children()); break;
		case VAR:  val = LightSymbol(e.var());         break;
		default: assert(false && "impossible");        break;
		}
	}
	void operator = (LightTree&& e) {
		switch (e.kind()) {
		case NODE: val = Node(e.rule(), std::move(e.children())); break;
		case VAR:  val = LightSymbol(e.var());         break;
		default: assert(false && "impossible");        break;
		}
	}

	bool operator == (const LightTree& e) const {
		if (kind() != e.kind()) return false;
		switch (kind()) {
		case NODE:
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
		assert(kind() == NODE);
		return std::get<Node>(val).rule;
	}
	const Type* type() const {
		return kind() == VAR ? var().type : rule()->term.type.get();
	}
	Children& children() {
		assert(kind() == NODE);
		return std::get<Node>(val).children;
	}
	const Children& children() const {
		assert(kind() == NODE);
		return std::get<Node>(val).children;
	}

	uint arity() const {
		switch (kind()) {
		case NODE: return std::get<Node>(val).children.size();
		case VAR:  return 0;
		default:   assert(0 && "impossible"); return -1;
		}
	}
	uint length() const {
		switch (kind()) {
		case NODE: {
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

private:
	typedef variant<Node, LightSymbol> Value;
	Value val;
};

struct Subst {
	Subst(bool ok = true) : ok(ok) { }
	Subst(LightSymbol v, const LightTree& t) : ok(true) {
		if (!(t.kind() == LightTree::VAR && t.var() == v)) {
			sub.emplace(v, t);
		}
	}
	Subst(const Subst& s) : ok(s.ok) {
		operator = (s);
	}
	Subst(Subst&& s) : ok(s.ok) {
		operator = (std::move(s));
	}
	void operator = (const Subst& s);
	void operator = (Subst&& s);

	bool consistent(const Subst& s) const;
	bool compose(const Subst& s);

	bool maps(LightSymbol v) const { return sub.find(v) != sub.end(); }

	map<LightSymbol, LightTree> sub;
	bool ok;
};

void compose(Subst& s1, const Subst& s2, bool full = true);
bool composable(const Subst& s1, const Subst& s2);

unique_ptr<rus::Tree> convert_tree_ptr(const LightTree&);
unique_ptr<LightTree> convert_tree_ptr(const rus::Tree&, ReplMode, uint i);
unique_ptr<LightTree> apply_ptr(const Subst&, const LightTree&);

inline rus::Tree convert_tree(const LightTree& t) {
	return rus::Tree(std::move(*convert_tree_ptr(t).release()));
}
inline LightTree convert_tree(const rus::Tree& t, ReplMode m, uint i) {
	return LightTree(std::move(*convert_tree_ptr(t, m, i).release()));
}
inline LightTree apply(const Subst& s, const LightTree& t) {
	return LightTree(std::move(*apply_ptr(s, t).release()));
}

rus::Expr convert_expr(const LightTree&);
rus::Substitution convert_sub(const Subst&);

string show(LightSymbol s, bool full = true);
string show(const LightTree&, bool full = true);
string show_ast(const LightTree&);
string show(const Subst& s);

inline ostream& operator << (ostream& os, const LightSymbol& s) {
	os << show(s); return os;
}

}}}
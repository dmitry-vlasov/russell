#pragma once

#include <rus_expr.hpp>
#include <rus_ast.hpp>

namespace mdl { namespace rus { namespace prover {

enum class ReplMode {
	KEEP_REPL,
	DENY_REPL,
	DEFAULT = KEEP_REPL
};

struct LightSymbol {
	LightSymbol() : lit(undef()), rep(false), type(nullptr)  { }
	LightSymbol(const rus::Symbol& s, ReplMode mode = ReplMode::DEFAULT) :
		lit(s.lit), rep(s.kind() == Symbol::VAR), type(s.kind() == Symbol::VAR ? s.type() : nullptr) {
		if (mode == ReplMode::DENY_REPL) {
			rep = false;
		}
	}
	LightSymbol(const LightSymbol& s) = default;
	LightSymbol(LightSymbol&& s) = default;
	bool is_undef() const { return lit == undef(); }
	bool is_def() const { return lit != undef(); }
	static uint undef() { return 0x7FFFFFFF; }
	uint literal() const { return lit; }

	bool operator == (const LightSymbol& s) const { return lit == s.lit; }
	bool operator != (const LightSymbol& s) const { return !operator ==(s); }
	bool operator < (const LightSymbol& s) const { return lit < s.lit; }

	void operator = (const LightSymbol& s) {
		lit  = s.lit;
		type = s.type;
		rep  = s.rep;
	}
	void operator = (LightSymbol&& s) {
		lit  = s.lit;
		type = s.type;
		rep  = s.rep;
	}

	struct Hash {
		typedef size_t result_type;
		typedef LightSymbol argument_type;
		size_t operator() (LightSymbol s) const {
			return hash(s.lit);
		}
	private:
		static std::hash<uint> hash;
	};

	uint lit:31;
	bool rep:1;
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
	Subst(bool ok = true) : sub(), ok(ok) { }
	Subst(uint v, const LightSymbol& t) : sub(), ok(true) {
		sub.emplace(v, t);
	}
	Subst(uint v, const LightTree& t) : sub(), ok(true) {
		sub.emplace(v, t);
	}
	Subst(LightSymbol v, const LightSymbol& t) : sub(), ok(true) {
		sub.emplace(v.literal(), t);
	}
	Subst(LightSymbol v, const LightTree& t) : sub(), ok(true) {
		sub.emplace(v.literal(), t);
	}
	Subst(const Subst& s) : sub(), ok(s.ok) {
		operator = (s);
	}
	Subst(Subst&& s) : sub(), ok(s.ok) {
		operator = (std::move(s));
	}
	void operator = (const Subst& s);
	void operator = (Subst&& s);

	bool join(uint v, const LightSymbol& t) {
		return join(v, LightTree(t));
	}
	bool join(uint v, const LightTree& t);
	bool join(uint v, LightTree&& t);
	bool join(const Subst* s) {
		return join(*s);
	}
	bool join(const Subst& s);
	bool join(Subst&& s);

	bool consistent(uint v, const LightTree& t);
	//bool consistent(const Subst& s);
	void compose(const Subst& s, bool full = true);

	bool maps(uint v) const { return sub.find(v) != sub.end(); }

	map<uint, LightTree> sub;
	bool ok;
};

Subst compose(const Subst& s1, const Subst& s2, bool full = true);
bool composable(const Subst& s1, const Subst& s2);

unique_ptr<rus::Tree> convert_tree_ptr(const LightTree&);
unique_ptr<LightTree> convert_tree_ptr(const rus::Tree&, ReplMode = ReplMode::DEFAULT);
unique_ptr<LightTree> apply_ptr(const Subst&, const LightTree&);
unique_ptr<LightTree> apply_ptr(const Substitution&, const LightTree&);

inline rus::Tree convert_tree(const LightTree& t) {
	return rus::Tree(std::move(*convert_tree_ptr(t).release()));
}
inline LightTree convert_tree(const rus::Tree& t, ReplMode m = ReplMode::DEFAULT) {
	return LightTree(std::move(*convert_tree_ptr(t, m).release()));
}
inline LightTree apply(const Subst& s, const LightTree& t) {
	return LightTree(std::move(*apply_ptr(s, t).release()));
}
inline LightTree apply(const Substitution& s, const LightTree& t) {
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

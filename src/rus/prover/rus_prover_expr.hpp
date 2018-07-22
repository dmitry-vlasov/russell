#pragma once

#include <rus_expr.hpp>
#include <rus_ast.hpp>

namespace mdl { namespace rus { namespace prover {

struct LightSymbol : public Literal {
	LightSymbol() = delete;
	LightSymbol(const rus::Symbol& s) : Literal(s), type(s.type()) { }
	LightSymbol(const LightSymbol& s) = default;
	LightSymbol(LightSymbol&& s) = default;

	struct Hash {
		typedef size_t result_type;
		typedef LightSymbol argument_type;
		size_t operator() (LightSymbol s) const {
			return hash(s.lit);
		}
	private:
		static std::hash<uint> hash;
	};
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
		const Rule* rule;
		Children    children;
	};

	LightTree() = delete;
	LightTree(const LightSymbol& v) : val(LightSymbol(v)) { }
	LightTree(const Rule* r, const Children& ch) : val(Node(r, ch)) { }
	LightTree(const LightTree& ex) = default;
	LightTree(LightTree&& ex) = default;

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

private:
	typedef variant<Node, LightSymbol> Value;
	Value val;
};

unique_ptr<rus::Tree> convert_tree(const LightTree&);
unique_ptr<LightTree> convert_tree(const rus::Tree&);
string show(LightSymbol s, bool full = true);
string show(const LightTree&, bool full = true);

inline ostream& operator << (ostream& os, const LightSymbol& s) {
	os << show(s); return os;
}

}}}

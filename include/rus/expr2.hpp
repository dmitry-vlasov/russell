#pragma once

#include "expr.hpp"

namespace mdl { namespace rus { namespace expr2 {

#define END_MARKER ";;"

struct Type;

struct Symbol : public mdl::Symbol {
	Symbol(string s, Type* t = nullptr);
	Symbol() : mdl::Symbol(), type(nullptr) { }
	Symbol(uint l): mdl::Symbol(l), type(nullptr) { }
	Symbol(const mdl::Symbol s, bool v = false) :
	mdl::Symbol(s.lit, v), type(nullptr) { }
	Symbol(const mdl::Symbol s, Type* tp, bool v = false) :
	mdl::Symbol(s.lit, v), type(tp) { }

	bool operator == (const Symbol& s) const {
		return mdl::Symbol::operator == (s) && type == s.type;
	}
	bool operator != (const Symbol& s) const {
		return !operator ==(s);
	}
	bool operator < (const Symbol& s) const {
		return
			type == s.type ?
			mdl::Symbol::operator < (s.lit) :
			type < s.type;
	}
	Type* type;
	struct Hash {
		typedef size_t result_type;
		typedef Symbol argument_type;
		size_t operator() (Symbol s) const {
			return hash(s.lit);
		}
	private:
		static std::hash<uint> hash;
	};
};

typedef vector<Symbol> Symbols;

string show(Symbol s, bool full = false);

inline ostream& operator << (ostream& os, Symbol s) {
	os << show(s);
	return os;
}


struct Expr {
	virtual ~Expr() { }
	virtual bool equal(const Expr*) const = 0;
	virtual Expr* clone() const = 0;
};

struct Rule;

struct RExpr : public Expr {
	typedef vector<unique_ptr<Expr>> Children;
	Rule* rule;
	Children children;
	RExpr(Rule* r) : rule(r), children() { }
	~RExpr() override { }
	bool equal(const Expr* e) const override {
		if (const RExpr* re = dynamic_cast<const RExpr*>(e)) {
			if (rule != re->rule) return false;
			return std::equal(
				children.begin(), children.end(),
				re->children.begin(), re->children.end(),
				[] (auto const& c1, auto const& c2) -> bool { return c1->equal(c2.get()); }
			);
		}
		return false;
	}
	Expr* clone() const override {
		RExpr* re = new RExpr (rule);
		for (auto const& c : children)
			re->children.push_back(unique_ptr<Expr>(c->clone()));
		return re;
	}
};

struct VExpr : public Expr {
	Symbol var;
	VExpr(const Symbol& v) : var(v) { }
	~VExpr() override { }
	bool equal(const Expr* e) const override {
		if (const VExpr* ve = dynamic_cast<const VExpr*>(e))
			return var == ve->var;
		return false;
	}
	Expr* clone() const override {
		return new VExpr(var);
	}
};

} // expr2

}} // mdl::rus

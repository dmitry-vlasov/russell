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
	LightSymbol() : lit(undef_value()), rep(false), ind(-1), type(nullptr)  { }
	LightSymbol(uint l, const Type* t, ReplMode mode, uint i) :
		lit(i == MATH_INDEX ? l :
			(i == ASSERTION_INDEX ? Lex::toInt(Lex::toStr(l) + "!") :
				Lex::toInt(Lex::toStr(l) + "_" + to_string(i - LightSymbol::INTERNAL_MIN_INDEX))
			)
		),
		rep(t),
		ind(i),
		type(t) {
		if (mode == ReplMode::DENY_REPL) {
			rep = false;
		}
	}
	LightSymbol(const rus::Symbol& s, ReplMode mode, uint i) :
		lit(i == MATH_INDEX ? s.lit() :
			(i == ASSERTION_INDEX ? Lex::toInt(Lex::toStr(s.lit()) + "!") :
				Lex::toInt(Lex::toStr(s.lit()) + "_" + to_string(i - LightSymbol::INTERNAL_MIN_INDEX))
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

	bool is_undef() const { return lit == undef_value(); }
	bool is_def() const { return lit != undef_value(); }
	uint literal() const { return lit; }
	static uint undef_value() { static uint val = uint(-1) >> 1; return val; }

	bool operator == (const LightSymbol& s) const { return lit == s.lit && ind == s.ind; }
	bool operator != (const LightSymbol& s) const { return !operator ==(s); }
	bool operator < (const LightSymbol& s) const {
		if (lit < s.lit) return true;
		else if (lit > s.lit) return false;
		else return ind < s.ind;
	}
	bool operator == (uint l) const { return lit == l; }
	bool operator != (uint l) const { return !operator ==(l); }

	LightSymbol& operator = (const LightSymbol& s) = default;
	LightSymbol& operator = (const Symbol& s) {
		lit = s.lit();
		type = s.type();
		ind = 0;
		rep = (s.kind() == Symbol::VAR);
		return *this;
	}

	uint lit:31;
	bool rep:1;
	uint ind;
	const Type* type;
};
string show(const set<uint>&);
string show(const vector<uint>&);
string show(const vector<bool>& v);
string show(const vector<LightSymbol>& v);
string show(LightSymbol s, bool full = true);

inline ostream& operator << (ostream& os, const LightSymbol& s) {
	os << show(s); return os;
}

}}}

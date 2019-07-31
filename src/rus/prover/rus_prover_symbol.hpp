#pragma once

#include "rus_ast.hpp"

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
	LightSymbol() : lit(undef_value()), rep(false), ind(-1), type(nullptr) { }
	explicit LightSymbol(uint l, bool r = true) : lit(l), rep(r), ind(-1), type(nullptr) { }
	LightSymbol(uint l, const Type* t, ReplMode mode = ReplMode::KEEP_REPL, uint i = MATH_INDEX) :
		lit(i == MATH_INDEX ? l : Lex::toInt(Lex::toStr(l) + "_" + to_string(i - LightSymbol::ASSERTION_INDEX))),
		rep(t),
		ind(i),
		type(t) {
		if (mode == ReplMode::DENY_REPL) {
			rep = false;
		}
	}
	LightSymbol(const rus::Symbol& s, ReplMode mode, uint i) :
		LightSymbol(s.lit(), s.kind() == Symbol::VAR ? s.type() : nullptr, mode, i) { }
	LightSymbol(const LightSymbol& s) = default;

	bool is_undef() const { return lit == undef_value(); }
	bool is_def() const { return lit != undef_value(); }
	uint literal() const { return lit; }
	static uint undef_value() { static uint val = uint(-1) >> 1; return val; }

	bool operator == (const LightSymbol& s) const { return lit == s.lit; }
	bool operator != (const LightSymbol& s) const { return !operator ==(s); }
	bool operator == (uint s) const { return lit == s; }
	bool operator != (uint s) const { return !operator ==(s); }
	bool operator < (const LightSymbol& s) const {
		if (lit < s.lit) return true;
		else if (lit > s.lit) return false;
		else return ind < s.ind;
	}

	LightSymbol& operator = (const LightSymbol& s) = default;
	LightSymbol& operator = (const Symbol& s) {
		lit = s.lit();
		type = s.type();
		ind = 0;
		rep = (s.kind() == Symbol::VAR);
		return *this;
	}

	string show(bool full = false) const {
		return (is_undef() ? "<UNDEF>" : Lex::toStr(lit)) + (full && rep ? "*" : "");
	}

	struct Hash {
		typedef size_t result_type;
		typedef Symbol argument_type;
		size_t operator() (const LightSymbol& s) const {
			return hash(s.lit);
		}
	private:
		static std::hash<uint> hash;
	};

	uint lit:31;
	bool rep:1;
	uint ind;
	const Type* type;
};

string show(const set<uint>&);
string show(const vector<uint>&);
string show(const vector<bool>& v);
string show(const vector<LightSymbol>& v);

inline ostream& operator << (ostream& os, const LightSymbol& s) {
	os << s.show(); return os;
}

struct VarProvider {
	LightSymbol makeFresh(LightSymbol v, ReplMode m = ReplMode::KEEP_REPL) {
		return makeFresh(v.lit, v.type, m);
	}
	LightSymbol makeFresh(uint l, const Type* t, ReplMode m = ReplMode::KEEP_REPL) {
		auto it = vars.find(l);
		uint fresh_ind = it != vars.end() ? it->second + 1 : LightSymbol::INTERNAL_MIN_INDEX;
		vars[l] = fresh_ind;
		return LightSymbol(l, t, m, fresh_ind);
	}

protected:
	map<uint, uint> vars;
};

}}}

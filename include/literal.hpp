#pragma once

#include "lex.hpp"

namespace mdl {

struct Literal {
	Literal(): lit(undef()), var(false) { }
	Literal(uint l, bool v = false) : lit(l), var(v) { }
	Literal(const Literal& s) : lit(s.lit), var(s.var) { }

	bool operator == (const Literal& s) const { return lit == s.lit; }
	bool operator != (const Literal& s) const { return !operator ==(s); }
	bool operator < (const Literal& s) const { return lit < s.lit; }
	bool is_undef() const { return lit == undef(); }
	bool is_turnstile() const {
		static uint t = Lex::toInt("|-"); return lit == t;
	}
	static bool is_undef(uint lit) { return lit == undef(); }
	static uint undef() { return 0x7FFFFFFF; }
	uint literal() const { return static_cast<uint>(lit); }
	string show() const { return Lex::toStr(lit); }

	uint lit:31;
	bool var:1;
};

inline ostream& operator << (ostream& os, Literal s) {
	os << Lex::toStr(s.lit) << " ";
	return os;
}

} // mdl

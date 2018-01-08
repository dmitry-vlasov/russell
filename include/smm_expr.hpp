#pragma once

#include "common.hpp"

namespace mdl { namespace smm {

struct Symbol {
	Symbol(): lit(undef()), var(false) { }
	Symbol(uint l, bool v = false) : lit(l), var(v) { }
	Symbol(const Symbol& s) : lit(s.lit), var(s.var) { }

	bool operator == (const Symbol& s) const { return lit == s.lit; }
	bool operator != (const Symbol& s) const { return !operator ==(s); }
	bool operator < (const Symbol& s) const { return lit < s.lit; }
	bool is_undef() const { return lit == undef(); }
	static bool is_undef(uint lit) { return lit == undef(); }
	static uint undef() { return 0x7FFFFFFF; }

	uint lit:31;
	bool var:1;
};

typedef vector<Symbol> Expr;

inline bool contains(const Expr& vect, uint lit) {
	for (auto it = vect.cbegin(); it != vect.cend(); ++ it) {
		if (it->lit == lit) return true;
	}
	return false;
}

inline bool contains(const Expr& vect, Symbol s) {
	return contains(vect, s.lit);
}

inline string show_sy(Symbol symb) {
	return Lex::toStr(symb.lit);
}

inline string show_ex(const Expr& vect) {
	string s;
	for (auto sy : vect) s += Lex::toStr(sy.lit) + " ";
	return s;
}

inline ostream& operator << (ostream& os, Symbol s) {
	os << Lex::toStr(s.lit);
	return os;
}

inline ostream& operator << (ostream& os, const Expr& ex) {
	os << show_ex(ex);
	return os;
}

}}

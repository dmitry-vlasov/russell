#pragma once

#include "literal.hpp"
#include "mm_sys.hpp"

namespace mdl { namespace mm {

typedef vector<Literal> Expr;

inline bool contains(const Expr& vect, uint lit) {
	for (auto it = vect.cbegin(); it != vect.cend(); ++ it) {
		if (it->lit == lit) return true;
	}
	return false;
}

inline bool contains(const Expr& vect, Literal s) {
	return contains(vect, s.lit);
}

inline string show_ex(const Expr& vect) {
	string s;
	for (auto sy : vect) s += Lex::toStr(sy.lit) + " ";
	return s;
}

inline ostream& operator << (ostream& os, const Expr& ex) {
	for (auto s : ex) os << s;
	return os;
}

typedef map<Literal, Expr> Subst;

inline string show(const Subst& subst) {
	string str;
	for (const auto& p : subst) {
		str += "\t" + p.first.show() + " = > " + show_ex(p.second) + "\n";
	}
	return str;
}

Expr apply_subst(const Subst& sub, const Expr& expr);

}} // mdl::mm2

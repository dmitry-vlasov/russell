/*****************************************************************************/
/* Project name:    smm - verifier for the Simplified MetaMath language      */
/* File name:       expr.hpp                                                 */
/* Description:     smm symbolic Expr                                        */
/* Copyright:       (c) 2006-2010 Dmitri Vlasov                              */
/* Author:          Dmitri Yurievich Vlasov, Novosibirsk, Russia             */
/* Email:           vlasov at academ.org                                     */
/* URL:             http://mathdevlanguage.sourceforge.net                   */
/* Modified by:                                                              */
/* License:         GNU General Public License Version 3                     */
/*****************************************************************************/

#pragma once

#include "common.hpp"

namespace mdl {

struct Symbol {
	enum Kind { VAR, CONST, NONE };
	Symbol(): lit(undef()), var(false), cst(false), end(false), rep(false), fin(false) { }
	Symbol(uint l, bool v = false) : lit(l), var(v), cst(false), end(false), rep(false), fin(false) { }
	Symbol(const Symbol& s) : lit(s.lit), var(s.var), cst(s.cst), end(s.end), rep(s.rep), fin(s.fin) { }

	bool operator == (const Symbol& s) const { return lit == s.lit; }
	bool operator != (const Symbol& s) const { return !operator ==(s); }
	bool operator < (const Symbol& s) const { return lit < s.lit; }
	bool is_undef() const { return lit == undef(); }
	static bool is_undef(uint lit) { return lit == undef(); }
	static uint undef() { return 0x07FFFFFF; }
	Kind kind() const {
		if (var && !cst) return VAR;
		if (cst && !var) return CONST;
		return NONE;
	}
	void set_kind(Kind k) {
		switch (k) {
		case VAR:   var = true; cst = false;  rep = true;  break;
		case CONST: var = false; cst = true;  rep = false; break;
		default:    var = false; cst = false; rep = false; break;
		}
	}

	uint lit:27;

	// Flags
	bool var:1; //< is variable
	bool cst:1; //< is constant
	bool end:1; //< is end of an expression
	bool rep:1; //< is replaceable variable
	bool fin:1; //< final node in a tree (in a horizontal iteration)
};

} // mdl

namespace std {
	template<>
	struct hash<mdl::Symbol> {
		size_t operator()(const mdl::Symbol& s) const noexcept {
			return s.lit;
		}
	};
}

namespace mdl {

typedef vector<Symbol> Vect;

inline bool contains(const Vect& vect, uint lit) {
	for (auto it = vect.cbegin(); it != vect.cend(); ++ it) {
		if (it->lit == lit) return true;
	}
	return false;
}

inline bool contains(const Vect& vect, Symbol s) {
	return contains(vect, s.lit);
}

inline void operator += (Vect& vect, Symbol s) {
	vect.push_back(s);
}

inline void operator += (Vect& vect_1, const Vect& vect_2) {
	for (auto s : vect_2) vect_1.push_back(s);
}

inline string show_sy(Symbol symb) {
	return Lex::toStr(symb.lit);
}
inline string show_id(uint lab) {
	return Lex::toStr(lab);
}

inline string show_ex(const Vect& vect) {
	string s;
	for (auto sy : vect) s += show_sy(sy) + " ";
	return s;
}

inline ostream& operator << (ostream& os, Symbol s) {
	os << show_sy(s);
	return os;
}

inline ostream& operator << (ostream& os, const Vect& ex) {
	os << show_ex(ex);
	return os;
}

}

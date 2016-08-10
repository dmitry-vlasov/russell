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

#include "std.hpp"
#define UNDEF_LIT 0x0FFFFFFF

namespace mdl {

struct Symbol {
	Symbol(): lit(UNDEF_LIT), var(false), end(false), rep(false), fin(false) { }
	Symbol(uint l, bool v = false) : lit (l), var (v), end(false), rep(false), fin(false) { }

	bool operator == (const Symbol& s) const {
		return lit == s.lit && var == s.var;
	}
	bool operator != (const Symbol& s) const {
		return !operator ==(s);
	}
	bool operator < (const Symbol& s) const {
		return lit < s.lit;
	}
	bool is_undef() const { return lit == UNDEF_LIT; }
	static bool is_undef(uint lit) { return lit == UNDEF_LIT; }
	uint lit:28;

	// Flags
	bool var:1; //< is variable
	bool end:1; //< is end of an expression
	bool rep:1; //< is replaceable var
	bool fin:1; //< final node in a tree (in a horizontal iteration)
};

struct Expr {
	Expr() : symbols() { }
	Expr(const Expr& ex) : symbols(ex.symbols) { }
	void push_back(Symbol s) {
		symbols.push_back(s);
	}
	bool contains(Symbol s) const {
		return contains(s.lit);
	}
	bool contains(uint lit) const {
		for (auto it = symbols.cbegin(); it != symbols.cend(); ++ it) {
			if (it->lit == lit)
				return true;
		}
		return false;
	}
	Expr& operator += (Symbol s) {
		symbols.push_back(s);
		return *this;
	}
	Expr& operator += (const Expr& ex) {
		for (auto s : ex.symbols)
			symbols.push_back(s);
		return *this;
	}
	bool operator == (const Expr& ex) const {
		return symbols == ex.symbols;
	}
	bool operator != (const Expr& ex) const {
		return !operator ==(ex);
	}
	bool undef() const {
		return symbols.size() == 0;
	}
	Symbol& operator [] (uint i) {
		return symbols[i];
	}
	Symbol operator [] (uint i) const {
		return symbols[i];
	}
	vector<Symbol> symbols;
};

string show_sy(Symbol);
string show_id(uint);

inline string show_ex(const Expr& expr) {
	string s;
	for (auto symb : expr.symbols)
		s += show_sy(symb) + " ";
	return s;
}

inline ostream& operator << (ostream& os, Symbol s) {
	os << show_sy(s);
	return os;
}

inline ostream& operator << (ostream& os, const Expr& ex) {
	os << show_ex(ex);
	return os;
}

}

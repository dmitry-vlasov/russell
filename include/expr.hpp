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

namespace mdl {

struct Symbol {
	Symbol(): lit(-1), var(false) { }
	Symbol(uint l) : lit (l), var (false) { }
	Symbol(uint l, bool v) : lit (l), var (v) { }

	bool operator == (const Symbol& s) const {
		return lit == s.lit && var == s.var;
	}
	bool operator != (const Symbol& s) const {
		return !operator ==(s);
	}
	bool operator < (const Symbol& s) const {
		return lit < s.lit;
	}
	uint lit;
	bool var;
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
	vector<Symbol> symbols;
};

string show(Symbol symb);

inline string show(const Expr& expr) {
	string s;
	for (auto symb : expr.symbols)
		s += show(symb) + " ";
	return s;
}

inline ostream& operator << (ostream& os, Symbol s) {
	os << show(s);
	return os;
}

inline ostream& operator << (ostream& os, const Expr& ex) {
	os << show(ex);
	return os;
}

}

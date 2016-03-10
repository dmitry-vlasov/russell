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
	Symbol(): literal(-1), isVar(false) { }
	Symbol(int lit, bool var = false) :
	literal (lit), isVar (var) {
	}

	bool operator == (const Symbol& s) const {
		return literal == s.literal && isVar == s.isVar;
	}
	bool operator != (const Symbol& s) const {
		return !operator ==(s);
	}
	bool operator < (const Symbol& s) const {
		return literal < s.literal;
	}
	uint literal;
	bool isVar;
};

struct Expr {
public :
	Expr(const Expr& ex) : symbols(ex.symbols) {
	}
	Expr() : symbols() {
	}
	void markVars(const Expr& vars) {
		for (auto it = symbols.begin(); it != symbols.end(); ++ it) {
			if (vars.contains(it->literal))
				it->isVar = true;
		}
	}
	void push_back(Symbol s) {
		symbols.push_back(s);
	}
	bool contains(Symbol s) const {
		return contains(s.literal);
	}
	bool contains(uint lit) const {
		for (auto it = symbols.cbegin(); it != symbols.cend(); ++ it) {
			if (it->literal == lit)
				return true;
		}
		return false;
	}
	Expr& operator += (Symbol s) {
		symbols.push_back(s);
		return *this;
	}
	Expr& operator += (const Expr& ex) {
		auto it = ex.symbols.cbegin();
		++ it;
		for (; it != ex.symbols.cend(); ++ it)
			symbols.push_back(*it);
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

ostream& operator << (ostream& os, const Symbol& symb);
ostream& operator << (ostream& os, const Expr& expr);
inline string show(Symbol symb) { ostringstream os; os << symb; return os.str(); }
inline string show(const Expr& expr) { ostringstream os; os << expr; return os.str(); }

}

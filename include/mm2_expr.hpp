#pragma once

#include "mm2_sys.hpp"

namespace mdl { namespace mm2 {

typedef mdl::Token<Source> Token;
typedef mdl::Tokenable<Source> Tokenable;
typedef mdl::Id<Source> Id;

struct Symbol : public Owner<Symbol> {
	Symbol() = delete;
	Symbol(const Symbol&) = delete;
	Symbol(uint l, bool v, const Token& t = Token()) : Owner(l, t), is_var(v) { }
	const bool is_var;
};

inline string show(const Symbol& s, bool full = false) {
	return Lex::toStr(s.id()) + (full ? (s.is_var ? "<var>" : "<cst>") : "") + ' ';
}

inline ostream& operator << (ostream& os, const Symbol& s) {
	os << show(s);
	return os;
}

typedef vector<User<Symbol>> Expr;

inline string show(const Expr& e) {
	string str;
	for (auto i = e.begin(); i != e.end(); ++i) str += show(*i->get());
	return str;
}

inline ostream& operator << (ostream& os, const Expr& ex) {
	os << show(ex);
	return os;
}

inline void dump(const Symbol& s) { cout << s; }
inline void dump(const Expr& e) { cout << e; }
inline size_t memvol(const Expr& ex) { return ex.capacity() * sizeof(Symbol); }

}} // mdl::mm2

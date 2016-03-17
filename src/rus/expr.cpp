#include "rus/globals.hpp"

namespace mdl {
namespace rus {

string show(Symbol s) {
	return rus::Rus::get().lex.symbs.toStr(s.lit);
}

string show(const Expr& ex) {
	string s;
	for (auto& e : ex.term)
		s += show(e.symb) + " ";
	return s;
}

}}

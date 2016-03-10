#include "expr.hpp"
#include "smm/ast.hpp"
#include "smm/globals.hpp"

namespace mdl {
 
ostream& operator << (ostream& os, const Symbol& symb) {
	os << smm::Smm::get().lex.symbols.toStr(symb.literal);
	return os;
}

ostream& operator << (ostream& os, const Expr& expr) {
	for (auto it = expr.symbols.cbegin(); it != expr.symbols.cend(); ++ it)
		os << *it << ' ';
	return os;
}
  
}

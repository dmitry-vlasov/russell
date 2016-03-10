#include "expr.hpp"
#include "smm/ast.hpp"
#include "smm/globals.hpp"

namespace mdl {
 
ostream& operator << (ostream& os, const Symbol& symb) {
	os << smm::Smm::get().lex.symbols.toStr(symb.lit);
	return os;
}

ostream& operator << (ostream& os, const Expr& expr) {
	for (auto symb : expr.symbols)
		os << symb << ' ';
	return os;
}
  
}

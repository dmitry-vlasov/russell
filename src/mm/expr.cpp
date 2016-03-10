#include "expr.hpp"
#include "mm/ast.hpp"
#include "mm/globals.hpp"

namespace mdl {
 
ostream& operator << (ostream& os, const Symbol& symb) {
	os << mm::Mm::get().lex.symbols.toStr(symb.lit);
	return os;
}

}

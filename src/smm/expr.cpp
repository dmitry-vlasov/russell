#include "expr.hpp"
#include "smm/ast.hpp"
#include "smm/globals.hpp"

namespace mdl {
 
void Symbol::show(string& str) const {
	str += smm::Smm::get().lex.symbols.toStr(literal);
	//if (isVar) str += '#';
}
  
}

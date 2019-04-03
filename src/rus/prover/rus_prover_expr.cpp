#include "rus_prover_expr.hpp"
#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

string show(LightSymbol s, bool full) {
	string ret;
	if (s.is_undef()) {
		ret += "<UNDEF>";
	} else {
		ret += Lex::toStr(s.lit);
	}
	if (full && s.rep) {
		ret += "*";
	}
	return ret;
}

}}}

#include "rus_parser_grammar.hpp"

namespace mdl { namespace rus {

void parse_spirit(uint label) {
	Source* src = Sys::mod().math.get<Source>().access(label);

	LocationIter iter(src->data().begin(), label);
	LocationIter end(src->data().end(), label);

	if (!parser::Grammar<LocationIter>::parse(iter, end, parser::unicode::space, *src) || iter != end) {
		throw Error("parsing failed", Lex::toStr(label));
	}
	src->parsed = true;
}

}} // mdl::rus

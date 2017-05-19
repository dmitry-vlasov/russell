#include "rus/parser/grammar.hpp"

namespace mdl { namespace rus {

Source* parse(uint label) {
	delete Sys::get().math.get<Source>().access(label);
	Source* src = new Source(label);
	src->read();
	LocationIter iter(src->data.begin(), label);
	LocationIter end(src->data.end(), label);
	if (!parser::Grammar<LocationIter>::parse(iter, end, parser::unicode::space, *src) || iter != end) {
		throw Error("parsing failed", Lex::toStr(label));
	}
	return src;
}

}} // mdl::rus

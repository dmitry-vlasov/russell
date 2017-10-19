#include "rus_parser_grammar.hpp"

namespace mdl { namespace rus {

void parse(uint label) {
	delete Sys::get().math.get<Source>().access(label);
	Source* src = new Source(label);
	src->read();
	LocationIter iter(src->data().begin(), label);
	LocationIter end(src->data().end(), label);

	//cout << "parsing: " << Lex::toStr(label) << endl;

	if (!parser::Grammar<LocationIter>::parse(iter, end, parser::unicode::space, *src) || iter != end) {
		throw Error("parsing failed", Lex::toStr(label));
	}
}

}} // mdl::rus

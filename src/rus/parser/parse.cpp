#include "rus/parser/grammar.hpp"

namespace mdl { namespace rus {

Source* parse(Path path) {
	string data;
	path.read(data);
	uint label = Lex::toInt(path.name);
	Source* src = new Source(label);
	LocationIter iter(data.begin(), label);
	LocationIter end(data.end(), label);
	if (!parser::Grammar<LocationIter>::parse(iter, end, parser::unicode::space, *src) || iter != end) {
		throw Error("parsing failed", path.name);
	}
	std::swap(data, src->data);
	return src;
}

}} // mdl::rus

#include "rus/sys.hpp"
#include "rus/parser/grammar.hpp"

namespace mdl { namespace rus { namespace parser {

namespace {
	uint ind = 0;
}

uint get_ind() { return ind; }
uint inc_ind() { return ind ++; }

} // parser

Source* parse(Path path) {
	path = path.verify();
	string data;
	path.read(data);
	Source* src = new Source(path.root, path.name);
	LocationIter iter(data.begin(), path.name);
	LocationIter end(data.end(), path.name);
	if (!parser::Grammar<LocationIter>::parse(iter, end, parser::unicode::space, *src) || iter != end) {
		throw Error("parsing failed", path.name);
	}
	std::swap(data, src->data);
	return src;
}

}} // mdl::rus

#include "rus/parser/grammar.hpp"
#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace parser {

namespace {
	uint ind = 0;
}

uint get_ind() { return ind; }
uint inc_ind() { return ind ++; }

} // parser

Source* parse(string name) {
	string orig_name = name;
	ifstream in = open_smart(name, Rus::get().config.root);
	string storage;
	in.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(in),
		std::istream_iterator<char>(),
		std::back_inserter(storage));

	LocationIter iter(storage.begin(), name);
	LocationIter end(storage.end(), name);
	Source* source = new Source(Rus::get().config.root, name);
	bool r = phrase_parse(iter, end, parser::Grammar<LocationIter>(), parser::unicode::space, *source);
	if (!r || iter != end) {
		throw Error("parsing failed", orig_name);
	}
	return source;
}

}} // mdl::rus

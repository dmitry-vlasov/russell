#include "mm/grammar.hpp"

namespace mdl { namespace mm {

Source* parse(string name) {
	ifstream in = open_smart(name, Mm::get().config.root);
	string storage;
	in.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(in),
		std::istream_iterator<char>(),
		std::back_inserter(storage));

	LocationIter iter(storage.begin(), name);
	LocationIter end(storage.end(), name);
	Source* source = new Source(Mm::get().config.root, name);
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, source);
	if (!r) {
		throw Error("parsing failed: false");
	}
	if (iter != end) {
		throw Error("parsing failed: iter != end");
	}
	return source;
}

}} // mdl::mm

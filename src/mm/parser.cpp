#include "mm/grammar.hpp"

namespace mdl { namespace mm {

Block* parse(const string& path) {
	ifstream in(path, std::ios_base::in);
	if (!in)
		throw Error("Could not open input file");

	string storage;
	in.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(in),
		std::istream_iterator<char>(),
		std::back_inserter(storage));

	LocationIter iter(storage.begin(), path);
	LocationIter end(storage.end(), path);
	Block* source = new Block(path);
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

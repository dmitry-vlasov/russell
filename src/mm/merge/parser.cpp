
#include "mm/globals.hpp"
#include "mm/merge/grammar.hpp"

namespace mdl { namespace mm { namespace merge {

void parse(const string& path) {
	ifstream is = open_smart(path, Mm::get().config.root);
	string storage;
	is.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(is),
		std::istream_iterator<char>(),
		std::back_inserter(storage));

	LocationIter iter(storage.begin(), path);
	LocationIter end(storage.end(), path);

	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space);
	if (!r || iter != end) {
		throw Error("parsing failed");
	}
}

}}} // mdl::mm::merge

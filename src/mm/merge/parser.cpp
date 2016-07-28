#include <boost/algorithm/string.hpp>

#include "mm/merge/grammar.hpp"

namespace mdl { namespace mm { namespace merge {

void parse(const string& name) {
	ifstream instream(name, std::ios_base::in);
	if (!instream.is_open())
		throw Error("Could not open input file");

	string storage;
	instream.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(instream),
		std::istream_iterator<char>(),
		std::back_inserter(storage));

	LocationIter iter(storage.begin(), name);
	LocationIter end(storage.end(), name);

	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space);
	if (!r || iter != end) {
		throw Error("parsing failed");
	}
}

}}} // mdl::mm::merge

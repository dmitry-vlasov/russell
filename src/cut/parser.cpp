#include "cut/grammar.hpp"

namespace mdl { namespace cut {

void parse(const string& path) {
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
	Cut::mod().source = new Section;
	Cut::mod().source->file = path;
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, Cut::mod().source);
	if (!r || iter != end) {
		throw Error("parsing failed");
	}
}

}} // mdl::cut

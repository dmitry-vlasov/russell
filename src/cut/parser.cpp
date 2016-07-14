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
	Section* source = new Section;
	Cut::mod().source = source;
	source->file = path;
	source->type = Type::SOURCE;
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, source);
	if (!r || iter != end) {
		throw Error("parsing failed");
	}
}

}} // mdl::cut

#include <boost/algorithm/string.hpp>

#include "cut/grammar.hpp"

namespace mdl { namespace cut {

void parse(const string& path) {
	ifstream in(path, std::ios_base::in);
	if (!in.is_open())
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
	source->file = Cut::get().config.out;
	source->path = Cut::get().config.out;
	boost::erase_last(source->file, ".mm");
	source->type = Type::SOURCE;
	Cut::mod().source = source;
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, source);
	if (!r || iter != end) {
		throw Error("parsing failed");
	}
}

}} // mdl::cut

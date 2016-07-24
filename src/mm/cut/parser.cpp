#include <boost/algorithm/string.hpp>

#include "mm/cut/grammar.hpp"

namespace mdl { namespace mm { namespace cut {

Section* parse(const string& path, const string& out) {
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
	source->path = out;
	source->file = out;
	source->dir = out.substr(0, out.find_last_of("/")) + "/";
	boost::erase_last(source->file, ".mm");
	source->type = Type::SOURCE;
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, source);
	if (!r || iter != end) {
		throw Error("parsing failed");
	}
	return source;
}

}}} // mdl::mm::cut

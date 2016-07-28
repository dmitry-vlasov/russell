#include <boost/algorithm/string.hpp>

#include "mm/cut/grammar.hpp"

namespace mdl { namespace mm { namespace cut {

Section* parse(const string& root, const string& in, const string& out) {
	ifstream instream(in, std::ios_base::in);
	if (!instream.is_open())
		throw Error("Could not open input file");

	string storage;
	instream.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(instream),
		std::istream_iterator<char>(),
		std::back_inserter(storage));

	LocationIter iter(storage.begin(), in);
	LocationIter end(storage.end(), in);
	Section* source = new Section;
	//source->path = out;
	//source->file = out;
	//source->dir = out.substr(0, out.find_last_of("/")) + "/";

	size_t slash_pos = in.find_last_of("/");
	size_t dot_pos = in.find_last_of(".");
	size_t len = in.size();
	if (slash_pos != string::npos) len -= slash_pos;
	if (dot_pos != string::npos)   len -= len - dot_pos;

	source->file = in.substr(slash_pos == string::npos ? 0 : slash_pos, len);
	source->dir = out + "/"; //out.substr(0, out.find_last_of("/")) + "/";
	source->path = source->dir + "/" + source->file + ".mm";

	//boost::erase_last(source->file, ".mm");
	source->type = Type::SOURCE;
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, source);
	if (!r || iter != end) {
		throw Error("parsing failed");
	}
	return source;
}

}}} // mdl::mm::cut

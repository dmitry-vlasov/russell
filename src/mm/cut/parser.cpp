#include <boost/algorithm/string.hpp>

#include "mm/cut/grammar.hpp"

namespace mdl { namespace mm { namespace cut {

Section* parse(const string& root, string in, const string& out) {
	/*ifstream is = open_smart(in, root);
	string storage;
	is.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(is),
		std::istream_iterator<char>(),
		std::back_inserter(storage));
	is.close();*/

	string storage;
	read_smart(storage, in, root);

	LocationIter iter(storage.begin(), in);
	LocationIter end(storage.end(), in);
	Section* source = new Section;

	size_t slash_pos = in.find_last_of("/");
	size_t dot_pos = in.find_last_of(".");
	size_t len = in.size();
	if (slash_pos != string::npos) len -= slash_pos;
	if (dot_pos != string::npos)   len -= len - dot_pos;

	source->file = in.substr(slash_pos == string::npos ? 0 : slash_pos, len);
	source->dir = out + "/";
	source->path = source->dir + "/" + source->file + ".mm";
	source->type = Type::SOURCE;
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, source);
	if (!r || iter != end) {
		throw Error("parsing failed", in);
	}
	return source;
}

}}} // mdl::mm::cut

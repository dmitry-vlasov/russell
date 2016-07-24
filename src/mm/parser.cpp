#include "mm/grammar.hpp"

namespace mdl { namespace mm {

Source* parse(const string& name) {
	string path =
		Mm::get().config.root.size() ?
		Mm::get().config.root + "/" + name :
		name;
	ifstream in(path, std::ios_base::in);
	if (!in.is_open())
		throw Error("Could not open input file", path);

	string storage;
	in.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(in),
		std::istream_iterator<char>(),
		std::back_inserter(storage));

	LocationIter iter(storage.begin(), path);
	LocationIter end(storage.end(), path);
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

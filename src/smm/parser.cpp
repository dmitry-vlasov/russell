#include "smm/grammar.hpp"

namespace mdl { namespace smm {

Source* parse(const string& name) {
	string path =
		Smm::get().config.root.size() ?
		Smm::get().config.root + "/" + name :
		name;
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
	Source* source = new Source(Smm::get().config.root, name);
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, *source);
	if (!r || iter != end) {
		throw Error("parsing failed");
	}
	return source;
}

}} // mdl::smm

#include "smm/grammar.hpp"

namespace mdl { namespace smm {

Source* parse(const string& name) {
	ifstream in = open_smart(name, Smm::get().config.root);

	string storage;
	in.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(in),
		std::istream_iterator<char>(),
		std::back_inserter(storage));

	LocationIter iter(storage.begin(), name);
	LocationIter end(storage.end(), name);
	Source* source = new Source(Smm::get().config.root, name);
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, *source);
	if (!r || iter != end) {
		throw Error("parsing failed");
	}
	return source;
}

}} // mdl::smm

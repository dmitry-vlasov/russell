#include "rus/grammar.hpp"
#include "rus/globals.hpp"

namespace mdl { namespace rus {

Source* parse(const string& path) {
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
	Source* source = new Source(path);
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, *source);
	if (!r || iter != end) {
		if (!r)
			cout << "R" << endl;
		else
			cout << "I" << endl;
		throw Error("parsing failed");
	}
	return source;
}

}} // mdl::rus

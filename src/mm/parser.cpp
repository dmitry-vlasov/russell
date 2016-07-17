#include "mm/grammar.hpp"

namespace mdl { namespace mm {

Block* parse(const string& path) {
	ifstream in(path, std::ios_base::in);
	if (!in.is_open())
		throw Error("Could not open input file");

	//cout << "LOADING:" << endl << path << endl;

	string storage;
	in.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(in),
		std::istream_iterator<char>(),
		std::back_inserter(storage));

	//cout << endl << endl << endl << "GOT:" << endl << storage << endl << endl;

	LocationIter iter(storage.begin(), path);
	LocationIter end(storage.end(), path);
	Block* source = new Block(path);
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, source);
	if (!r) {
		throw Error("parsing failed: false");
	}
	if (iter != end) {
		throw Error("parsing failed: iter != end");
	}

	//cout << "FINISHED:" << endl << path << endl << "\n\n\n\n\n" << endl;

	return source;
}

}} // mdl::mm

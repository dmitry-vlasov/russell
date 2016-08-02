#include "smm/grammar.hpp"

namespace mdl { namespace smm {

/*
Source* parse(string name) {
	ifstream in = open_smart(name, Smm::get().config.root);
	string storage;
	in.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(in),
		std::istream_iterator<char>(),
		std::back_inserter(storage));
	in.close();

	LocationIter iter(storage.begin(), name);
	LocationIter end(storage.end(), name);
	Source* source = new Source(Smm::get().config.root, name);
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, *source);
	if (!r || iter != end) {
		throw Error("parsing failed", name);
	}
	return source;
}
*/

Source* parse(string name) {
	/*string data;
	open_smart(data, name, Rus::get().config.root);
	Source* src = new Source(Rus::get().config.root, name);
	parse(src, data);
	return src;*/
	typedef parser::Grammar<LocationIter> Parser;
	return mdl::parse<Source, Parser>(name, Smm::get().config.root, parser::ascii::space);
}

}} // mdl::smm

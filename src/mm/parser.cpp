#include "mm/grammar.hpp"

namespace mdl { namespace mm {
/*
Source* create(string name, string& data) {
	ifstream in = open_smart(name, Mm::get().config.root);
	in.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(in),
		std::istream_iterator<char>(),
		std::back_inserter(data));
	in.close();
	return new Source(Mm::get().config.root, name);
}

void parse(string name) {
	ifstream in = open_smart(name, Mm::get().config.root);
	string storage;
	in.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(in),
		std::istream_iterator<char>(),
		std::back_inserter(storage));
	in.close();

	LocationIter iter(storage.begin(), name);
	LocationIter end(storage.end(), name);
	Source* source = new Source(Mm::get().config.root, name);
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, source);
	if (!r || iter != end) {
		throw Error("parsing failed", name);
	}
	return source;
}

void parse(Source* src, string& data) {
	typedef parser::Grammar<LocationIter> Parser;
	LocationIter iter(data.begin(), src->name);
	LocationIter end(data.end(), src->name);
	if (!phrase_parse(iter, end, Parser(), parser::unicode::space, *src) || iter != end) {
		throw Error("parsing failed", src->name);
	}
}
*/

Source* parse(string name) {
	/*string data;
	read_smart(data, name, data);
	LocationIter iter(data.begin(), name);
	LocationIter end(data.end(), name);
	Source* source = new Source(Mm::get().config.root, name);
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, source);
	if (!r || iter != end) {
		throw Error("parsing failed", name);
	}
	return source;*/
	typedef parser::Grammar<LocationIter> Parser;
	return mdl::parse<Source, Parser>(name, Mm::get().config.root, parser::ascii::space);
}

}} // mdl::mm

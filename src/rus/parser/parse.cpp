#include "rus/parser/grammar.hpp"
#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace parser {

namespace {
	uint ind = 0;
}

uint get_ind() { return ind; }
uint inc_ind() { return ind ++; }

} // parser

/*
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
	open_smart(data, name, Rus::get().config.root);
	Source* src = new Source(Rus::get().config.root, name);
	parse(src, data);
	return src;*/
	typedef parser::Grammar<LocationIter> Parser;
	return mdl::parse<Source, Parser>(name, Rus::get().config.root, parser::unicode::space);
}

}} // mdl::rus

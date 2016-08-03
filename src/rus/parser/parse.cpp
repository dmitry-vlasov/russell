#include "rus/parser/grammar.hpp"
#include "rus/globals.hpp"

namespace mdl { namespace rus { namespace parser {

namespace {
	uint ind = 0;
}

uint get_ind() { return ind; }
uint inc_ind() { return ind ++; }

} // parser

Source* parse(string name) {
	typedef parser::Grammar<LocationIter> Parser;
	return mdl::parse<Source, Parser>(name, Rus::get().config.root, parser::unicode::space);
}

}} // mdl::rus

#include "spirit_grammar.hpp"

namespace mdl { namespace mm {

Source* parse_spirit(string name) {
	typedef parser::Grammar<LocationIter> Parser;
	return mdl::parse<Source, Parser>(name, Mm::get().config.root, parser::ascii::space);
}

}} // mdl::mm

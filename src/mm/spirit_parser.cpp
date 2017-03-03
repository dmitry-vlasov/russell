#include "spirit_grammar.hpp"

namespace mdl { namespace mm {

Source* parse_spirit(string name) {
	typedef parser::Grammar<LocationIter> Parser;
	return mdl::parse<Source, Parser>(name, System::get().config.in.root, parser::ascii::space);
}

}} // mdl::mm

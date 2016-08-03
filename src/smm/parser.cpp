#include "smm/grammar.hpp"

namespace mdl { namespace smm {

Source* parse(string name) {
	typedef parser::Grammar<LocationIter> Parser;
	return mdl::parse<Source, Parser>(name, Smm::get().config.root, parser::ascii::space);
}

}} // mdl::smm

#include "mm/grammar.hpp"

namespace mdl { namespace mm { namespace ctags {

Source* parse(string name) {
	typedef parser::Grammar<LocationIter> Parser;
	return mdl::parse<Source, Parser>(name, Mm::get().config.root, parser::ascii::space);
}

}}} // mdl::mm

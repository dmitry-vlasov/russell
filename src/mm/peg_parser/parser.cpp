#include "mm/grammar.hpp"
#include "parser.hpp"

namespace mdl { namespace mm {

Source* peg_parse(string name) {
	peg_parser::Parser p;

	int i = p.parse(name);
	//return mdl::parse<Source, Parser>(name, Mm::get().config.root, parser::ascii::space);
	return nullptr;
}

}} // mdl::mm

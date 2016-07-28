
#define BOOST_SPIRIT_USE_PHOENIX_V3

#include "mm/merge/parser.hpp"

namespace mdl { namespace mm { namespace merge {

template <typename Iterator>
Grammar<Iterator>::Grammar() : Grammar::base_type(source, "merge") {
		using qi::lit;
		using qi::lexeme;
		using namespace qi::labels;

		const phoenix::function<Add> add;
		const phoenix::function<Include> include;

		contents  %= lexeme[+(ascii::char_ - "$[")];
		inclusion %= lit("$[") > lexeme[+(ascii::char_ - "$]")] > "$]";
		source = + (inclusion [include(_1)] | contents  [add(_1)] );

		qi::on_error<qi::fail>(
			source,
			std::cout << phoenix::val("Syntax error. Expecting ") << _4
			<< phoenix::val(" here: \n") << _3 << phoenix::val("\n")
			<< phoenix::val("code: \n") <<phoenix::construct<wrapper<>>(_3));
		initNames();
	}

}}} // mdl::mm::merge

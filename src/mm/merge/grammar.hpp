
#define BOOST_SPIRIT_USE_PHOENIX_V3

#include "mm/merge/parser.hpp"

namespace mdl { namespace mm { namespace merge {

template <typename Iterator>
Grammar<Iterator>::Grammar() : Grammar::base_type(source, "merge") {
		using qi::lit;
		using qi::uint_;
		using qi::lexeme;
		using qi::eps;
		using namespace qi::labels;
		using phoenix::at_c;
		using phoenix::new_;

		const phoenix::function<Add> add;
		const phoenix::function<Include> include;
		const phoenix::function<MakeString> makeString;


		contents = lexeme[*(ascii::char_ - "$[")] [_val = makeString(_1)];
		inclusion =
			  lit("$[")
			> lexeme[*(ascii::char_ - "$]")] [_val = makeString(_1)]
			> "$]";

		source =
			+ (
				inclusion [include(_1)] |
				contents  [add(_1)]
			);

		qi::on_error<qi::fail>(
			source,
			std::cout << phoenix::val("Syntax error. Expecting ") << _4
			<< phoenix::val(" here: \n") << _3 << phoenix::val("\n")
			<< phoenix::val("code: \n") <<phoenix::construct<wrapper<>>(_3));
		initNames();
	}

}}} // mdl::mm::merge

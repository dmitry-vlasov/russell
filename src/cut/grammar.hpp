#define BOOST_SPIRIT_USE_PHOENIX_V3

#include "cut/parser.hpp"

namespace mdl { namespace cut {

template <typename Iterator>
Grammar<Iterator>::Grammar() : Grammar::base_type(source, "cut") {
		using qi::lit;
		using qi::uint_;
		using qi::lexeme;
		using qi::eps;
		using namespace qi::labels;
		using phoenix::at_c;
		using phoenix::new_;

		const phoenix::function<Add> add;
		const phoenix::function<MakeString> makeString;


		border =
			  lit(PARAGRAPH_STR) [_val = cut::Type::PARAGRAPH]
			| lit(CHAPTER_STR)   [_val = cut::Type::CHAPTER]
			| lit(PART_STR)      [_val = cut::Type::PART];

		header %= lexeme[+(ascii::char_ - FULL_PART_STR)];

		section =
			  lit("$(\n")                           [_val = new_<cut::Section>()]
			> lexeme[*(ascii::char_ - '#' - '=')] [at_c<1>(*_val) = makeString(_1)]
			> border                              [at_c<0>(*_val) = _1]
			> lexeme[+(ascii::char_ - '#' - '=')] [at_c<2>(*_val) = makeString(_1)]
			> border
			> lexeme[*(ascii::char_ - "$)")]      [at_c<3>(*_val) = makeString(_1)]
			> lit("$)\n")                         [add(_val)];

		contents %=
			lexeme[+(ascii::char_ - FULL_PARAGRAPH_STR - FULL_CHAPTER_STR - FULL_PART_STR)];

		source =
			  header [add(_1)]
			> + (
				section |
				contents [add(_1)]
			);

		qi::on_error<qi::fail>(
			source,
			std::cout << phoenix::val("Syntax error. Expecting ") << _4
			<< phoenix::val(" here: \n") << _3 << phoenix::val("\n")
			<< phoenix::val("code: \n") <<phoenix::construct<wrapper<>>(_3));
		initNames();
	}

}} // mdl::mm

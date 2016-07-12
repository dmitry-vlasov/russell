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

		paragraph =
			  lit("$(\n")                         [_val = new_<cut::Paragraph>()]
			> lexeme[+(ascii::char_ - PARAGRAPH)]
			> lit(PARAGRAPH)
			> lexeme[+(ascii::char_ - PARAGRAPH)] [at_c<1>(*_val) = makeString(_1)]
			> lit(PARAGRAPH)
			> lit("\n")
			> lexeme[+(ascii::char_ - "$)")]      [at_c<2>(*_val) = makeString(_1)]
			> lit("$)\n")                         [add(_val)];

		chapter =
			  lit("$(\n")                         [_val = new_<cut::Chapter>()]
			> lexeme[+(ascii::char_ - CHAPTER)]
			> lit(CHAPTER)
			> lexeme[+(ascii::char_ - CHAPTER)]   [at_c<1>(*_val) = makeString(_1)]
			> lit(CHAPTER)
			> lit("\n")
			> lexeme[+(ascii::char_ - "$)")]      [at_c<2>(*_val) = makeString(_1)]
			> lit("$)\n")                         [add(_val)];

		part =
			  lit("$(\n")                         [_val = new_<cut::Part>()]
			> lexeme[+(ascii::char_ - PART)]
			> lit(PART)
			> lexeme[+(ascii::char_ - PART)]      [at_c<1>(*_val) = makeString(_1)]
			> lit(PART)
			> lit("\n")
			> lexeme[+(ascii::char_ - "$)")]      [at_c<2>(*_val) = makeString(_1)]
			> lit("$)\n")                         [add(_val)];

		contents %=
			lexeme[+(ascii::char_ - FULL_PARAGRAPH - FULL_CHAPTER - FULL_PART)];

		source =
			+ (
				part      |
				chapter   |
				paragraph |
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

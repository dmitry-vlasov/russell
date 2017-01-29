
#define BOOST_SPIRIT_USE_PHOENIX_V3

#include <boost/spirit/include/phoenix_object.hpp>

#include "../spirit_parser.hpp"

namespace mdl { namespace mm { namespace ctags {

template <typename Iterator>
Grammar<Iterator>::Grammar() : Grammar::base_type(source, "russell") {
	using qi::lit;
	using qi::uint_;
	using qi::lexeme;
	using namespace qi::labels;
	using phoenix::construct;
	using phoenix::ref;
	using phoenix::val;

	const phoenix::function<CreateLabel> createLabel;
	const phoenix::function<AddTag> addTag;

	symbol = lexeme[+(ascii::char_ - '$' - ascii::space)];
	label  = lexeme[+(ascii::char_ - '$' - ascii::space)];
	path   = lexeme[+(ascii::char_ - '$' - ascii::space)];

	expr  = + (symbol | comment);
	proof = + label > "$.";
	const char* beg = "";
	const char* end = "";

	theorem =
		  label     [_a = _1]
		>> lit("$p")[val_ = construct<Tag>(_a, val(Tag.PROVABLE))]
		> expr > lit("$=") > proof;
	axiom =
		   label    [_a = _1]
		>> lit("$a")[val_ = construct<Tag>(_a, val(Tag.AXIOMATTIC))]
		> expr > lit("$.");
	essential =
		  label     [_a = _1]
		>> lit("$e")[val_ = construct<Tag>(_a, val(Tag.ESSENTIAL))]
		> expr > lit("$.");
	floating =
		  label     [_a = _1]
		>> lit("$f")[val_ = construct<Tag>(_a, val(Tag.FLOATING))]
		> expr > lit("$.");

	disjointed = lit("$d") > expr > "$.";
	variables  = lit("$v") > expr > "$.";
	constants  = lit("$c") > expr > "$.";
	inclusion  = lit("$[") > path > "$]";
	comment    = lit("$(") >> lexeme[*(ascii::char_ - "$)")] >> "$)";
	node %= (
		constants  |
		variables  |
		disjointed |
		block      |
		floating   [phoenix::at_c<2>(r_1).insert(_1)] |
		essential  [phoenix::at_c<2>(r_1).insert(_1)] |
		axiom      [phoenix::at_c<2>(r_1).insert(_1)] |
		theorem    [phoenix::at_c<2>(r_1).insert(_1)] );

	block = lit("${") > *(comment | node) > "$}";

	source = * (comment | node(val_) | inclusion);

	//qi::on_success(assertion, setLocation(_val, _1));
	qi::on_error<qi::fail>(
		source,
		std::cout << phoenix::val("Syntax error. Expecting ") << _4
		<< phoenix::val(" here: \n") << _3 << phoenix::val("\n")
		<< phoenix::val("code: \n") << phoenix::construct<wrapper<>>(_3));
	initNames();
}

}}} // mdl::mm::parser

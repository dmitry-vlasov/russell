#pragma once

#define BOOST_SPIRIT_USE_PHOENIX_V3

#include "smm/parser.hpp"

namespace mdl { namespace smm { namespace parser {

template<typename Iterator>
Grammar<Iterator>::Grammar() : Grammar::base_type(source, "russell") {
	using qi::lit;
	using qi::uint_;
	using qi::lexeme;
	using namespace qi::labels;
	using phoenix::at_c;
	using phoenix::push_back;
	using phoenix::new_;

	const phoenix::function<LabelToInt>     labelToInt;
	const phoenix::function<SymbolToInt>    symbolToInt;
	const phoenix::function<AddToMath>      addToMath;
	const phoenix::function<ParseInclusion> parseInclusion;
	const phoenix::function<SetLocation<Iterator>> setLocation;
	const phoenix::function<CreateRef>      createRef;
	const phoenix::function<MakeString>     makeString;

	symbol = lexeme[+(ascii::char_ - '$' - ascii::space)] [at_c<0>(_val) = symbolToInt(_1)];
	label  = lexeme[+(ascii::char_ - '$' - ascii::space)] [_val = labelToInt(_1)];
	path   = lexeme[+(ascii::char_ - '$' - ascii::space)];
	expr   = + (symbol [push_back(at_c<0>(_val), _1)] | comment);

	ref = (
		(hyp_refs  [_a = _1] > uint_ [_val = createRef(_a, _1, _r1)]) |
		(prop_refs [_a = _1] > label [_val = createRef(_a, _1, _r1)])
	);
	proof =
		qi::eps     [_val = new_<smm::Proof>()]
		> + ref(_r1)[push_back(phoenix::at_c<0>(*_val), _1)]
		> lit("$.") [phoenix::at_c<1>(*_val) = _r1];
	provable =
		lit("p")    [at_c<0>(_val) = false]
		> label     [at_c<1>(_val) = _1]
		> "$p"
		> expr      [at_c<2>(_val) = _1]
		> "$=";
	axiomatic =
		lit("a")    [at_c<0>(_val) = true]
		> label     [at_c<1>(_val) = _1]
		> "$a"
		> expr      [at_c<2>(_val) = _1]
		> "$.";
	essential =
		lit("e")    [_val = new_<smm::Essential>()]
		> uint_     [at_c<0>(*_val) = _1]
		> "$e"
		> expr      [at_c<1>(*_val) = _1]
		> "$.";
	inner =
		lit("i")    [_val = new_<smm::Inner>()]
		> uint_     [at_c<0>(*_val) = _1]
		> "$f"
		> expr      [at_c<1>(*_val) = _1]
		> "$.";
	floating =
		lit("f")    [_val = new_<smm::Floating>()]
		> uint_     [at_c<0>(*_val) = _1]
		> "$f"
		> expr      [at_c<1>(*_val) = _1]
		> "$.";
	disjointed =
		lit("$d")   [_val = new_<smm::Disjointed>()]
		> expr      [at_c<0>(*_val) = _1]
		> "$.";
	variables =
		lit("$v")   [_val = new_<smm::Variables>()]
		> expr      [at_c<0>(*_val) = _1]
		> "$.";
	assertion =
		lit("${")        [_val = new_<smm::Assertion>()]
		> *variables     [push_back(phoenix::at_c<0>(*_val), _1)]
		> *disjointed    [push_back(phoenix::at_c<1>(*_val), _1)]
		> *essential     [push_back(phoenix::at_c<2>(*_val), _1)]
		> *floating      [push_back(phoenix::at_c<3>(*_val), _1)]
		> *inner         [push_back(phoenix::at_c<4>(*_val), _1)]
		>  (axiomatic    [phoenix::at_c<5>(*_val) = _1] |
			(provable    [phoenix::at_c<5>(*_val) = _1]
			> proof(_val)[phoenix::at_c<6>(*_val) = _1])
		)
		> lit("$}")      [addToMath(_val)];
	constants =
		lit("$c")        [_val = new_<smm::Constants>()]
		> expr           [phoenix::at_c<0>(*_val) = _1]
		> lit("$.")      [addToMath(_val)];
	inclusion = lit("$[") > path [_val = parseInclusion(_1)] > "$]";
	comment = lit("$(") >> lexeme[*(ascii::char_ - "$)")] [_val = new_<smm::Comment>(makeString(_1))] >> "$)";
	source = +(
		constants [push_back(at_c<2>(_val), phoenix::construct<Node>(_1))] |
		assertion [push_back(at_c<2>(_val), phoenix::construct<Node>(_1))] |
		inclusion [push_back(at_c<2>(_val), phoenix::construct<Node>(_1))] |
		comment   [push_back(at_c<2>(_val), phoenix::construct<Node>(_1))]
	);

	qi::on_success(assertion, setLocation(_val, _1));
	qi::on_error<qi::fail>(
		source,
		std::cout << phoenix::val("Syntax error. Expecting ") << _4
		<< phoenix::val(" here: \n") << _3 << phoenix::val("\n")
		<< phoenix::val("code: \n") <<phoenix::construct<wrapper<>>(_3));
	initNames();
}

}}} //mdl::smm:parser

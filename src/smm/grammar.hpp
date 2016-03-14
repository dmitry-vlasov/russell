#pragma once

#define BOOST_SPIRIT_USE_PHOENIX_V3

#include "smm/parser.hpp"

namespace mdl { namespace smm {

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

		symbol = lexeme[+(ascii::char_ - '$' - ascii::space)] [at_c<0>(_val) = symbolToInt(_1)];
		label  = lexeme[+(ascii::char_ - '$' - ascii::space)] [_val = labelToInt(_1)];
		path   = lexeme[+(ascii::char_ - '$' - ascii::space)];

		expr_e = + (symbol [push_back(at_c<0>(_val), _1)] | comment) > "$.";
		expr_p = + (symbol [push_back(at_c<0>(_val), _1)] | comment)> "$=";
		expr_f =
			  symbol [push_back(at_c<0>(_val), _1)]
			> symbol [push_back(at_c<0>(_val), _1)]
			> "$.";

		a_ref = lit('a') [at_c<0>(_val) = Ref::PREF_A] > label [at_c<1>(_val) = _1];
		p_ref = lit('p') [at_c<0>(_val) = Ref::PREF_P] > label [at_c<1>(_val) = _1];
		e_ref = lit('e') [at_c<0>(_val) = Ref::PREF_E] > uint_ [at_c<1>(_val) = _1];
		f_ref = lit('f') [at_c<0>(_val) = Ref::PREF_F] > uint_ [at_c<1>(_val) = _1];
		i_ref = lit('i') [at_c<0>(_val) = Ref::PREF_I] > uint_ [at_c<1>(_val) = _1];

		proof =
			qi::eps     [_val = new_<smm::Proof>()]
			> +(a_ref | p_ref | e_ref | f_ref | i_ref) [push_back(phoenix::at_c<0>(*_val), _1)]
			> lit("$.") [phoenix::at_c<1>(*_val) = _r1];
		provable =
			lit("p")    [at_c<0>(_val) = false]
			> label     [at_c<1>(_val) = _1]
			> "$p"
			> expr_p    [at_c<2>(_val) = _1];
		axiomatic =
			lit("a")    [at_c<0>(_val) = true]
			> label     [at_c<1>(_val) = _1]
			> "$a"
			> expr_e    [at_c<2>(_val) = _1];
		essential =
			lit("e")
			> uint_     [at_c<0>(_val) = _1]
			> "$e"
			> expr_e    [at_c<1>(_val) = _1];
		inner =
			lit("i")
			> uint_     [at_c<0>(_val) = _1]
			> "$f"
			> expr_f    [at_c<1>(_val) = _1];
		floating =
			lit("f")
			> uint_     [at_c<0>(_val) = _1]
			> "$f"
			> expr_f    [at_c<1>(_val) = _1];
		disjointed %= lit("$d") > expr_e;
		variables  %= lit("$v") > expr_e;
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
			lit("$c") [_val = new_<smm::Constants>()]
			> expr_e  [phoenix::at_c<0>(*_val) = _1]
			> qi::eps [addToMath(_val)];
		inclusion = lit("$[")
			> path [_val = parseInclusion(_1)]
			> "$]";
		comment = lit("$(") >> lexeme[*(ascii::char_ - "$)")] >> "$)";
		source = +(
			constants [push_back(at_c<2>(_val), phoenix::construct<Node>(_1))] |
			assertion [push_back(at_c<2>(_val), phoenix::construct<Node>(_1))] |
			inclusion [push_back(at_c<2>(_val), phoenix::construct<Node>(_1))] |
			comment);

		qi::on_success(assertion, setLocation(_val, _1));
		qi::on_error<qi::fail>(
			source,
			std::cout << phoenix::val("Syntax error. Expecting ") << _4
			<< phoenix::val(" here: \n") << _3 << phoenix::val("\n")
			<< phoenix::val("code: \n") <<phoenix::construct<wrapper<>>(_3));
		initNames();
	}


}} //mdl::smm

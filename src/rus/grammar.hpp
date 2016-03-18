#pragma once

#define BOOST_SPIRIT_USE_PHOENIX_V3

#include "rus/parser.hpp"

namespace mdl { namespace rus {

template<typename Iterator>
Grammar<Iterator>::Grammar() : Grammar::base_type(source, "russell") {
	using qi::lit;
	using qi::uint_;
	using qi::lexeme;
	using qi::eps;
	using namespace qi::labels;
	using phoenix::at_c;
	using phoenix::push_back;
	using phoenix::new_;
	using phoenix::val;

	const phoenix::function<IdToInt>     idToInt;
	const phoenix::function<SymbToInt>   symbToInt;
	const phoenix::function<AddSymbol>   addSymbol;
	const phoenix::function<ParseExpr>   parseExpr;
	const phoenix::function<FindType>    findType;
	const phoenix::function<AddDisjVar>  addDisjVar;
	const phoenix::function<NewDisjSet>  newDisjSet;
	const phoenix::function<AddToMath>   addToMath;
	const phoenix::function<ParseImport> parseImport;
	const phoenix::function<SetLocation<Iterator>> setLocation;

	symb = lexeme[+(ascii::char_ - ';' - ascii::space)] [at_c<0>(_val) = symbToInt(_1)];
	id   = lexeme[ + ascii::char_("a-zA-Z0-9_.\\-")]    [_val = idToInt(_1)];
	path = lexeme[+(ascii::char_ - ';' - ascii::space)];

	expr = + (symb [addSymbol(_val, _1)] | comment) > eps [parseExpr(_val, _r1, _r2)];

	disj =
		lit("(")
		> + (
			eps      [newDisjSet(phoenix::at_c<0>(_val))]
			> + symb [addDisjVar(phoenix::at_c<0>(_val), _1)]
		) % ","
		> ")";

	vars =
		* ( !lit(")")
		> symb       [_a =_1]
		> ":" > id   [phoenix::at_c<2>(_a) = findType(_1)]
		> eps        [push_back(phoenix::at_c<0>(_val), _a)]
		);
	/*
	prop =
		lit("prop")  [_val = new_<Prop>]
		> ? uint_    [phoenix::at_c<0>(_val) = _1]
		> ":"
		> id        [_a = _1]
		> "=" > "|-"
		> expr(_a)  [phoenix::at_c<1>(_val) = _1]
		> lit(";")  [parseExpr(phoenix::at_c<1>(_val), _a)];

	hyp =
		lit("hyp")  [_val = new_<Hyp>]
		> ? uint_    [phoenix::at_c<0>(_val) = _1]
		> ":"
		> id        [_a = _1]
		> "=" > "|-"
		> expr(_a)  [phoenix::at_c<1>(_val) = _1]
		> lit(";")  [parseExpr(phoenix::at_c<1>(_val), _a)];

	axiom =
		lit("axiom")[_val = new_<Axiom>]
		> eps       [_a = phoenix::at_c<0>(*_val)]
		> id        [phoenix::at_c<0>(_a) = _1]
		> "("
		> vars      [phoenix::at_c<1>(_a) = _1]
		> ")"
		> - disjs    [phoenix::at_c<2>(_a) = _1]
		> "{"
		> - ( + (hyp [push_back(phoenix::at_c<3>(_a), _1)]) > bar)
		> + (prop   [push_back(phoenix::at_c<4>(_a), _1)])
		> "}"       [addToMath(_val)];
	*/
	rule =
		lit("rule")  [_val = new_<Rule>()]
		> - id       [phoenix::at_c<0>(*_val) = _1]
		> "("
		> vars       [phoenix::at_c<2>(*_val) = _1]
		> ")" > "{" > "term" > ":"
		> id         [phoenix::at_c<1>(*_val) = findType(_1)]
		> "=" > "#"
		> expr(phoenix::at_c<1>(*_val), val(false))
					 [phoenix::at_c<3>(*_val) = _1]
		> ";"
		> lit("}")   [addToMath(_val)];

	type =
		lit("type") [_val = new_<Type>()]
		> id        [phoenix::at_c<0>(*_val) = _1]
		>> -(lit(":")
			>  id [push_back(phoenix::at_c<1>(*_val), findType(_1))] % ","
		)
		> lit(";")  [addToMath(_val)];

	constant =
		lit("constant") [_val = new_<Const>()] > "{"
		> "symbol"
		> symb          [phoenix::at_c<0>(*_val) = _1]
		> lit(";")
		>> -(
			lit("ascii")
			> symb          [phoenix::at_c<1>(*_val) = _1]
			> lit(";")
			>> -(
				lit("latex")
				> symb      [phoenix::at_c<2>(*_val) = _1]
				> lit(";")
			)
		)
		> lit("}")      [addToMath(_val)];

	import = lit("import") > path [_val = parseImport(_1)] > ";";

	comment = lit("/*") >> lexeme[*(ascii::char_ - "*/")] >> "*/" |
			  lit("//") >> lexeme[*(ascii::char_ - "\n")] >> "\n";
	source = +(
		constant [push_back(at_c<1>(at_c<2>(_val)), phoenix::construct<Node>(_1))] |
		type     [push_back(at_c<1>(at_c<2>(_val)), phoenix::construct<Node>(_1))] |
		rule     [push_back(at_c<1>(at_c<2>(_val)), phoenix::construct<Node>(_1))] |
	/*	axiom    [push_back(at_c<1>(at_c<2>(_val)), phoenix::construct<Node>(_1))] |
		def      [push_back(at_c<1>(at_c<2>(_val)), phoenix::construct<Node>(_1))] |
		theorem  [push_back(at_c<1>(at_c<2>(_val)), phoenix::construct<Node>(_1))] |
		proof    [push_back(at_c<1>(at_c<2>(_val)), phoenix::construct<Node>(_1))] |*/
		comment);

	//qi::on_success(assertion, setLocation(_val, _1));
	qi::on_error<qi::fail>(
		source,
		std::cout << phoenix::val("Syntax error. Expecting ") << _4
		<< phoenix::val(" here: \n") << _3 << phoenix::val("\n")
		<< phoenix::val("code: \n") <<phoenix::construct<wrapper<>>(_3));
	initNames();
}

}} //mdl::rus

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
	const phoenix::function<ParseTerm>   parseTerm;

	const phoenix::function<PushVars>    pushVars;
	const phoenix::function<PopVars>     popVars;
	const phoenix::function<AddVars>     addVars;

	const phoenix::function<FindType>    findType;
	const phoenix::function<FindTheorem> findTheorem;
	const phoenix::function<FindAxiom>   findAxiom;
	const phoenix::function<FindDef>     findDef;

	const phoenix::function<CreateStepRef> createStepRef;
	const phoenix::function<GetProp>     getProp;
	const phoenix::function<GetStep>     getStep;

	const phoenix::function<AddDisjVar>  addDisjVar;
	const phoenix::function<NewDisjSet>  newDisjSet;

	const phoenix::function<AddToMath>   addToMath;
	const phoenix::function<ParseImport> parseImport;
	const phoenix::function<SetLocation<Iterator>> setLocation;

	bar  = lexeme[lit("-----")] >> * ascii::char_('-');
	symb = lexeme[+(ascii::char_ - ';' - ascii::space)] [at_c<0>(_val) = symbToInt(_1)];
	id   = lexeme[+ ascii::char_("a-zA-Z0-9_.\\-")]    [_val = idToInt(_1)];
	path = lexeme[+(ascii::char_ - ';' - ascii::space)];

	term = + (symb [addSymbol(_val, _1)] | comment) > eps [parseTerm(_val, _r1, phoenix::ref(var_stack))];
	expr = + (symb [addSymbol(_val, _1)] | comment) > eps [parseExpr(_val, _r1, phoenix::ref(var_stack))];

	disj =
		lit("disjointed") > "("
		> + (
			eps      [newDisjSet(phoenix::at_c<0>(_val))]
			> + symb [addDisjVar(phoenix::at_c<0>(_val), _1)]
		) % ","
		> ")";

	vars =
		( !lit(")")
		> symb       [_a =_1]
		> ":" > id   [phoenix::at_c<2>(_a) = findType(_1)]
		> eps        [push_back(phoenix::at_c<0>(_val), _a)]
		) % ","
		> eps        [addVars(phoenix::ref(var_stack), _val)];

	prop =
		lit("prop")  [_val = new_<Prop>()]
		> - uint_    [phoenix::at_c<0>(*_val) = _1 - 1]
		> ":"
		> id         [_a = _1]
		> "=" > "|-"
		> expr(findType(_a))
		             [phoenix::at_c<1>(*_val) = _1]
		> lit(";");

	hyp =
		lit("hyp")   [_val = new_<Hyp>()]
		> - uint_    [phoenix::at_c<0>(*_val) = _1 - 1]
		> ":"
		> id         [_a = _1]
		> "=" > "|-"
		> expr(findType(_a))
		             [phoenix::at_c<1>(*_val) = _1]
		> lit(";");

	assertion =
		  id         [phoenix::at_c<0>(*_r1) = _1]
		> lit("(")   [pushVars(phoenix::ref(var_stack))]
		> vars       [phoenix::at_c<1>(*_r1) = _1]
		> ")"
		> - disj     [phoenix::at_c<2>(*_r1) = _1]
		> "{"
		> - ( + (hyp [push_back(phoenix::at_c<3>(*_r1), _1)]) > bar )
		> + (prop    [push_back(phoenix::at_c<4>(*_r1), _1)])
		> lit("}")   [pushVars(phoenix::ref(var_stack))];

	refs =
		lit("(")
		> - ((
			("hyp"  > uint_ [push_back(_val, createStepRef(_1 - 1, _r1, val(Ref::HYP)))])  |
			("prop" > uint_ [push_back(_val, createStepRef(_1 - 1, _r1, val(Ref::PROP)))]) |
			("step" > uint_ [push_back(_val, createStepRef(_1 - 1, _r1, val(Ref::STEP)))])
		) % ",")
		> ")";

	step =
		eps     [_val = new_<Step>(_r1)]
		> uint_ [phoenix::at_c<0>(*_val) = _1 - 1]
		> ":"
		> id    [_a = _1]
		> "="
		> (
			(lit("axm") [phoenix::at_c<2>(*_val) = val(Step::AXM)]
			//> eps       [_b = val(Step::AXM)]
			> id        [phoenix::at_c<1>(phoenix::at_c<3>(*_val)) = findAxiom(_1)]
			) |
			(lit("thm") [phoenix::at_c<2>(*_val) = val(Step::THM)]
			> id        [phoenix::at_c<3>(phoenix::at_c<3>(*_val)) = findTheorem(_1)]
			//> eps       [_b = val(Step::THM)]
			) |
			(lit("def") [phoenix::at_c<2>(*_val) = val(Step::DEF)]
			> id        [phoenix::at_c<2>(phoenix::at_c<3>(*_val)) = findDef(_1)]
			//> eps       [_b = val(Step::DEF)]
			) |
			(lit("claim") [phoenix::at_c<2>(*_val) = val(Step::CLAIM)]
			//> eps       [_b = val(Step::CLAIM)]
			) |
			(lit("?")   [phoenix::at_c<2>(*_val) = val(Step::NONE)]
			//> eps       [_b = val(Step::NONE)]
			)
		)
		> refs(_r1) [phoenix::at_c<4>(*_val) = _1]
		> "|-"
		> expr(findType(_a))
		        [phoenix::at_c<1>(*_val) = _1]
		> lit(";");

	qed =
		lit("prop") [_val = new_<Qed>()]
		> eps       [_a =  0]
		> - uint_   [_a = _1]
		> lit("=")  [phoenix::at_c<0>(*_val) = getProp(_a - 1, _r1)]
		> "step"
		> uint_     [phoenix::at_c<1>(*_val) = getStep(_1 - 1, _r1)]
		> ";";

	proof_elem = (
		("step"  > step(_r1) [_val = phoenix::construct<Proof::Elem>(_1)]) |
		("qed"   > qed(_r1)  [_val = phoenix::construct<Proof::Elem>(_1)]) |
		("var"   > vars      [phoenix::at_c<1>(*_r1) = _1] > lit(";"))
	);

	proof_body =
		lit("{")   [pushVars(phoenix::ref(var_stack))]
		> + proof_elem(_r1)[push_back(phoenix::at_c<2>(*_r1), _1)]
		> lit("}") [popVars(phoenix::ref(var_stack))];

	proof =
		lit("proof") [_val = new_<Proof>()]
		> - (!lit("of") > - id [phoenix::at_c<0>(*_val) = _1])
		> "of"
		> id         [phoenix::at_c<3>(*_val) = findTheorem(_1)]
		> eps        [pushVars(phoenix::ref(var_stack))]
		> eps        [addVars(phoenix::ref(var_stack), phoenix::at_c<3>(*_val))]
		> proof_body(_val)
		> eps        [popVars(phoenix::ref(var_stack))]
		> eps        [addToMath(_val)];

	theorem =
		lit("theorem") [_val = new_<Theorem>()]
		> eps          [_a = &phoenix::at_c<0>(*_val)]
		> assertion(_a)
		> eps          [addToMath(_val)];

	axiom =
		lit("axiom") [_val = new_<Axiom>()]
		> eps        [_a = &phoenix::at_c<0>(*_val)]
		> assertion(_a)
		> eps        [addToMath(_val)];

	rule =
		lit("rule")  [_val = new_<Rule>()]
		> - id       [phoenix::at_c<0>(*_val) = _1]
		> lit("(")   [pushVars(phoenix::ref(var_stack))]
		> vars       [phoenix::at_c<2>(*_val) = _1]
		> ")" > "{" > "term" > ":"
		> id         [phoenix::at_c<1>(*_val) = findType(_1)]
		> "=" > "#"
		> term(_val) [phoenix::at_c<3>(*_val) = _1]
		> ";"
		> lit("}")   [addToMath(_val)]
		> eps        [popVars(phoenix::ref(var_stack))];

	type =
		lit("type") [_val = new_<Type>()]
		> id        [phoenix::at_c<0>(*_val) = _1]
		> - (lit(":")
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
		axiom    [push_back(at_c<1>(at_c<2>(_val)), phoenix::construct<Node>(_1))] |
	//	def      [push_back(at_c<1>(at_c<2>(_val)), phoenix::construct<Node>(_1))] |
		theorem  [push_back(at_c<1>(at_c<2>(_val)), phoenix::construct<Node>(_1))] |
		proof    [push_back(at_c<1>(at_c<2>(_val)), phoenix::construct<Node>(_1))] |
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

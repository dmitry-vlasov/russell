#pragma once

#define BOOST_SPIRIT_USE_PHOENIX_V3
#define BOOST_SPIRIT_UNICODE

#include "parse.hpp"

namespace mdl { namespace rus { namespace parser {

template<typename Iterator>
Grammar<Iterator>::Grammar(Source* src) : Grammar::base_type(source, "russell"), var_stack() {
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
	const phoenix::function<CreateSymb>  createSymb;

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
	const phoenix::function<AssembleDef> assembleDef;
	const phoenix::function<SetToken<Iterator>> setToken;
	const phoenix::function<MakeString>  makeString;
	const phoenix::function<DeleteComment> deleteComment;
	const phoenix::function<AppendComment> appendComment;

	bar  = lexeme[lit("-----")] >> * unicode::char_('-');
	var  = lexeme[+(unicode::char_ - END_MARKER - unicode::space - unicode::char_("),"))] [_val = createSymb(_1)];
	symb = lexeme[+(unicode::char_ - END_MARKER - unicode::space)] [_val = createSymb(_1)];
	id   = lexeme[+ unicode::char_("a-zA-Z0-9_.\\-")]            [_val = idToInt(_1)];
	path = lexeme[+(unicode::char_ - END_MARKER - unicode::space)];

	term  = + (symb [addSymbol(_val, _1)] | comment [deleteComment(_1)]) > eps [parseTerm(_val, _r1, phoenix::ref(var_stack))];
	expr  = + (symb [addSymbol(_val, _1)] | comment [deleteComment(_1)]) > eps [parseExpr(_val, _r1, phoenix::ref(var_stack))];
	plain = + (symb [addSymbol(_val, _1)] | comment [deleteComment(_1)]) > eps [phoenix::at_c<0>(_val) = _r1];

	disj =
		lit("disjointed") > "("
		> + ( (!(lit(")") | lit(",")))
			> eps    [newDisjSet(phoenix::at_c<0>(_val))]
			> + var  [addDisjVar(phoenix::at_c<0>(_val), _1)]
		) % ","
		> ")";

	vars =
		( !lit(")")
		> var        [_a =_1]
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
		> lit(END_MARKER);

	hyp =
		lit("hyp")   [_val = new_<Hyp>()]
		> - uint_    [phoenix::at_c<0>(*_val) = _1 - 1]
		> ":"
		> id         [_a = _1]
		> "=" > "|-"
		> expr(findType(_a))
		             [phoenix::at_c<1>(*_val) = _1]
		> lit(END_MARKER);

	assertion =
		id           [phoenix::at_c<0>(*_r1) = _1]
		> lit("(")   [pushVars(phoenix::ref(var_stack))]
		> - vars     [phoenix::at_c<1>(*_r1) = _1]
		> ")"
		> - disj     [phoenix::at_c<2>(*_r1) = _1]
		> "{"
		> - ( + (hyp [push_back(phoenix::at_c<3>(*_r1), _1)]) > bar )
		> + (prop    [push_back(phoenix::at_c<4>(*_r1), _1)])
		> lit("}")   [popVars(phoenix::ref(var_stack))];

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
		> expr(findType(_a)) [phoenix::at_c<1>(*_val) = _1]
		> lit(END_MARKER);

	qed =
		lit("prop") [_val = new_<Qed>()]
		> eps       [_a =  0]
		> - uint_   [_a = _1]
		> lit("=")  [phoenix::at_c<0>(*_val) = getProp(_a - 1, _r1)]
		> "step"
		> uint_     [phoenix::at_c<1>(*_val) = getStep(_1 - 1, _r1)]
		> END_MARKER;

	proof_elem = (
		("step"  > step(_r1) [_val = phoenix::construct<Proof::Elem>(_1)]) |
		("qed"   > qed(_r1)  [_val = phoenix::construct<Proof::Elem>(_1)])
	);

	proof_body =
		lit("{")   [pushVars(phoenix::ref(var_stack))]
		> - ("var" > vars [phoenix::at_c<1>(*_r1) = _1] > lit(END_MARKER))
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

	def = lit("definition") [_val = new_<Def>()]
		> eps        [_a = &phoenix::at_c<0>(*_val)]
		> id         [phoenix::at_c<0>(*_a) = _1]
		> lit("(")   [pushVars(phoenix::ref(var_stack))]
		> - vars     [phoenix::at_c<1>(*_a) = _1]
		> ")"
		> - disj     [phoenix::at_c<2>(*_a) = _1]
		> "{"
		> - ( + (hyp [push_back(phoenix::at_c<3>(*_a), _1)]) )
		> "defiendum" > ":"
		> id         [_b = findType(_1)]
		> "=" > "#"
		> expr(_b)    [phoenix::at_c<1>(*_val) = _1]
		> END_MARKER
		> "definiens" > ":"
		> id         [_b = findType(_1)]
		> "=" > "#"
		> expr(_b)   [phoenix::at_c<2>(*_val) = _1]
		> END_MARKER
		> bar
		> "prop" > ":"
		> id         [_b = findType(_1)]
		> "=" > "|-"
		> plain(_b)  [phoenix::at_c<3>(*_val) = _1]
		> END_MARKER
		> eps        [assembleDef(_val, phoenix::ref(var_stack))]
		> lit("}")   [pushVars(phoenix::ref(var_stack))]
		> eps        [addToMath(_val)];


	rule =
		lit("rule")  [_val = new_<Rule>()]
		> - id       [phoenix::at_c<0>(*_val) = _1]
		> lit("(")   [pushVars(phoenix::ref(var_stack))]
		> - vars     [phoenix::at_c<2>(*_val) = _1]
		> ")" > "{" > "term" > ":"
		> id         [phoenix::at_c<1>(*_val) = findType(_1)]
		> "=" > "#"
		> term(_val) [phoenix::at_c<3>(*_val) = _1]
		> END_MARKER
		> lit("}")   [addToMath(_val)]
		> eps        [popVars(phoenix::ref(var_stack))];

	type =
		lit("type")
		> id        [_a = _1]
		> - (lit(":")
			>  id [push_back(_b, findType(_1))] % ","
		)
		> lit(END_MARKER)  [_val = new_<Type>(_a, _b)]
		> eps [addToMath(_val)];

	constant =
		lit("constant") > "{"
		> lit("symbol")
		> symb          [_a = _1]
		> lit(END_MARKER)
		> -(
			lit("ascii")
			> symb          [_b = _1]
			> lit(END_MARKER)
		)
		> -(
			lit("latex")
			> symb      [_c = _1]
			> lit(END_MARKER)
		)
		> lit("}")      [_val = new_<Const>(_a, _b, _c)];

	import = lit("import") > path [_val = parseImport(_1, phoenix::val(src))] > END_MARKER;

	comment_text %= lexeme[+(unicode::char_ - "*/" - "/*")];
	comment_ml =
		   lit("/*")                        [_val = new_<Comment>()]
		>> *(
			comment_text [phoenix::at_c<0>(*_val) = _1] |
			comment_ml [appendComment(_val, _1)]
		)
		>> lit("*/");

	comment_sl =
		   lit("//")                        [_val = new_<Comment>()]
		>> lexeme[+(unicode::char_ - "\n")] [phoenix::at_c<0>(*_val) = makeString(_1)];

	comment %= comment_ml | comment_sl;

	source =
		eps [at_c<0>(_val) = new_<Theory>()]
		> +(
			import   [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(_1))] |
			constant [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(_1))] |
			type     [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(_1))] |
			rule     [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(_1))] |
			axiom    [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(_1))] |
			def      [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(_1))] |
			theorem  [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(_1))] |
			proof    [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(_1))] |
			comment  [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(_1))]
		);

	qi::on_success(term,      setToken(phoenix::at_c<3>(_val), _1, _3, phoenix::val(src)));
	qi::on_success(expr,      setToken(phoenix::at_c<3>(_val), _1, _3, phoenix::val(src)));
	qi::on_success(plain,     setToken(phoenix::at_c<3>(_val), _1, _3, phoenix::val(src)));
	qi::on_success(comment,   setToken(phoenix::at_c<1>(*_val), _1, _3, phoenix::val(src)));
	qi::on_success(import,    setToken(phoenix::at_c<2>(*_val), _1, _3, phoenix::val(src)));
	qi::on_success(constant,  setToken(phoenix::at_c<3>(*_val), _1, _3, phoenix::val(src)));
	qi::on_success(vars,      setToken(phoenix::at_c<1>(_val), _1, _3, phoenix::val(src)));
	qi::on_success(disj,      setToken(phoenix::at_c<1>(_val), _1, _3, phoenix::val(src)));
	qi::on_success(type,      setToken(phoenix::at_c<4>(*_val), _1, _3, phoenix::val(src)));
	qi::on_success(rule,      setToken(phoenix::at_c<4>(*_val), _1, _3, phoenix::val(src)));
	qi::on_success(hyp,       setToken(phoenix::at_c<2>(*_val), _1, _3, phoenix::val(src)));
	qi::on_success(prop,      setToken(phoenix::at_c<2>(*_val), _1, _3, phoenix::val(src)));
	qi::on_success(step,      setToken(phoenix::at_c<6>(*_val), _1, _3, phoenix::val(src)));
	qi::on_success(qed,       setToken(phoenix::at_c<2>(*_val), _1, _3, phoenix::val(src)));
	qi::on_success(proof,     setToken(phoenix::at_c<6>(*_val), _1, _3, phoenix::val(src)));

	qi::on_success(axiom,   setToken(phoenix::at_c<5>(phoenix::at_c<0>(*_val)), _1, _3, phoenix::val(src)));
	qi::on_success(theorem, setToken(phoenix::at_c<5>(phoenix::at_c<0>(*_val)), _1, _3, phoenix::val(src)));
	qi::on_success(def,     setToken(phoenix::at_c<5>(phoenix::at_c<0>(*_val)), _1, _3, phoenix::val(src)));

	//qi::on_success(theory, setToken(phoenix::at_c<2>(*_val), _1, _3));

	qi::on_error<qi::fail>(
		source,
		std::cout << phoenix::val("Syntax error. Expecting ") << _4
		<< phoenix::val(" here: \n") << _3 << phoenix::val("\n")
		<< phoenix::val("code: \n") << phoenix::construct<wrapper<>>(_3));
	initNames();
}

}}} //mdl::rus::parser

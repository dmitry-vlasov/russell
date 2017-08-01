#pragma once

#define BOOST_SPIRIT_USE_PHOENIX_V3
#define BOOST_SPIRIT_UNICODE

#include "rus_parser.hpp"

namespace mdl { namespace rus { namespace parser {

template<typename Iterator>
Grammar<Iterator>::Grammar(Source* src) : Grammar::base_type(source, "russell") {
	using qi::lit;
	using qi::uint_;
	using qi::lexeme;
	using qi::eps;
	using qi::labels::_val;
	using qi::labels::_r1;
	using qi::labels::_r2;
	using qi::labels::_a;
	using qi::labels::_b;
	using qi::labels::_c;
	using qi::labels::_d;
	using qi::labels::_e;
	using phoenix::at_c;
	using phoenix::push_back;
	using phoenix::new_;
	using phoenix::val;

	const phoenix::function<IdToInt>     idToInt;
	const phoenix::function<SymbToInt>   symbToInt;
	const phoenix::function<AddSymbol>   addSymbol;
	const phoenix::function<CreateSymb>  createSymb;

	const phoenix::function<ParseExpr>   parseExpr;
	const phoenix::function<ParsePlain>  parsePlain;

	const phoenix::function<PushVars>    pushVars;
	const phoenix::function<PopVars>     popVars;
	const phoenix::function<AddVars>     addVars;

	const phoenix::function<FindType>    findType;
	const phoenix::function<FindTheorem> findTheorem;
	const phoenix::function<SetType>     setType;

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

	bar   = lexeme[lit("-----")] >> * unicode::char_('-');
	liter = lexeme[+(unicode::char_ - END_MARKER - unicode::space)] [_val = symbToInt(qi::labels::_1)];
	var   = lexeme[+(unicode::char_ - END_MARKER - unicode::space - unicode::char_("),"))] [_val = createSymb(qi::labels::_1)];
	symb  = lexeme[+(unicode::char_ - END_MARKER - unicode::space)] [_val = createSymb(qi::labels::_1)];
	id    = lexeme[+ unicode::char_("a-zA-Z0-9_.\\-")]              [_val = idToInt(qi::labels::_1)];
	path  = lexeme[+(unicode::char_ - END_MARKER - unicode::space)];

	term  = + (symb [addSymbol(_val, qi::labels::_1)] | comment [deleteComment(qi::labels::_1)]) > eps [parseExpr(_val, _r1, phoenix::ref(var_stack))];
	expr  = + (symb [addSymbol(_val, qi::labels::_1)] | comment [deleteComment(qi::labels::_1)]) > eps [parseExpr(_val, _r1, phoenix::ref(var_stack))];
	plain = + (symb [addSymbol(_val, qi::labels::_1)] | comment [deleteComment(qi::labels::_1)]) > eps [parsePlain(_val, _r1)];

	disj =
		lit("disjointed") > "("
		> + ( (!(lit(")") | lit(",")))
			> eps    [newDisjSet(phoenix::at_c<0>(_val))]
			> + var  [addDisjVar(phoenix::at_c<0>(_val), qi::labels::_1)]
		) % ","
		> ")";

	vars =
		( !lit(")")
		> var        [_a = qi::labels::_1]
		> ":" > id   [setType(_a, qi::labels::_1)]
		> eps        [push_back(phoenix::at_c<0>(_val), _a)]
		) % ","
		> eps        [addVars(phoenix::ref(var_stack), _val)];

	prop =
		lit("prop")
		> - uint_    [_val = new_<Prop>(qi::labels::_1 - 1)]
		> ":"
		> id         [_a = qi::labels::_1]
		> "=" > "|-"
		> expr(_a)
		             [phoenix::at_c<1>(*_val) = qi::labels::_1]
		> lit(END_MARKER);

	hyp =
		lit("hyp")
		> - uint_    [_val = new_<Hyp>(qi::labels::_1 - 1)]
		> ":"
		> id         [_a = qi::labels::_1]
		> "=" > "|-"
		> expr(_a)
		             [phoenix::at_c<1>(*_val) = qi::labels::_1]
		> lit(END_MARKER);

	ref =
		("hyp"  > uint_ [_val = createStepRef(qi::labels::_1 - 1, _r1, val(Ref::HYP))])  |
		("prop" > uint_ [_val = createStepRef(qi::labels::_1 - 1, _r1, val(Ref::PROP))]) |
		("step" > uint_ [_val = createStepRef(qi::labels::_1 - 1, _r1, val(Ref::STEP))]);

	refs =
		lit("(") > - (ref(_r1) [push_back(_val, qi::labels::_1)] % ",") > ")";

	step =
		uint_ [_a = qi::labels::_1 - 1] > ":" > id [_b = qi::labels::_1] > "="
		> (
			(lit("axm") [_c = val(Step::ASS), _d = val(Assertion::AXM)] > id [_e = qi::labels::_1]) |
			(lit("thm") [_c = val(Step::ASS), _d = val(Assertion::THM)] > id [_e = qi::labels::_1]) |
			(lit("def") [_c = val(Step::ASS), _d = val(Assertion::DEF)] > id [_e = qi::labels::_1]) |
			(lit("claim") [_c = val(Step::CLAIM)]) |
			(lit("?")     [_c = val(Step::NONE)])
		)
		> eps [_val = new_<Step>(_a, _c, _d, _e, _r1)]
		> refs(_r1) [phoenix::at_c<4>(*_val) = qi::labels::_1]
		> "|-"
		> expr(_b) [phoenix::at_c<1>(*_val) = qi::labels::_1]
		> lit(END_MARKER);

	qed =
		lit("prop") [_val = new_<Qed>()]
		> eps       [_a =  0]
		> - uint_   [_a = qi::labels::_1]
		> lit("=")  [phoenix::at_c<0>(*_val) = getProp(_a - 1, _r1)]
		> "step"
		> uint_     [phoenix::at_c<1>(*_val) = getStep(qi::labels::_1 - 1, _r1)]
		> END_MARKER;

	proof_elem = (
		("step"  > step(_r1) [_val = phoenix::construct<Proof::Elem>(qi::labels::_1)]) |
		("qed"   > qed(_r1)  [_val = phoenix::construct<Proof::Elem>(qi::labels::_1)])
	);

	proof_body =
		lit("{")   [pushVars(phoenix::ref(var_stack))]
		> - ("var" > vars [phoenix::at_c<1>(*_r1) = qi::labels::_1] > lit(END_MARKER))
		> + proof_elem(_r1)[push_back(phoenix::at_c<2>(*_r1), qi::labels::_1)]
		> lit("}") [popVars(phoenix::ref(var_stack))];

	proof =
		lit("proof") [_a = phoenix::val(-1)]
		> - (!lit("of") > - id [_a = qi::labels::_1])
		> "of"
		> id         [_val = new_<Proof>(findTheorem(qi::labels::_1), _a)]
		> eps        [pushVars(phoenix::ref(var_stack))]
		> eps        [addVars(phoenix::ref(var_stack), phoenix::at_c<3>(*_val))]
		> proof_body(_val)
		> eps        [popVars(phoenix::ref(var_stack))]
		> eps        [addToMath(_val)];

	theorem =
		lit("theorem")
		> id         [_val = new_<Theorem>(qi::labels::_1)]
		> lit("(")   [pushVars(phoenix::ref(var_stack))]
		> - vars     [phoenix::at_c<0>(*_val) = qi::labels::_1]
		> ")"
		> - disj     [phoenix::at_c<1>(*_val) = qi::labels::_1]
		> "{"
		> - ( + (hyp [push_back(phoenix::at_c<2>(*_val), qi::labels::_1)]) > bar )
		> + (prop    [push_back(phoenix::at_c<3>(*_val), qi::labels::_1)])
		> lit("}")   [popVars(phoenix::ref(var_stack))]
		> eps        [addToMath(_val)];

	axiom =
		lit("axiom")
		> id         [_val = new_<Axiom>(qi::labels::_1)]
		> lit("(")   [pushVars(phoenix::ref(var_stack))]
		> - vars     [phoenix::at_c<0>(*_val) = qi::labels::_1]
		> ")"
		> - disj     [phoenix::at_c<1>(*_val) = qi::labels::_1]
		> "{"
		> - ( + (hyp [push_back(phoenix::at_c<2>(*_val), qi::labels::_1)]) > bar )
		> + (prop    [push_back(phoenix::at_c<3>(*_val), qi::labels::_1)])
		> lit("}")   [popVars(phoenix::ref(var_stack))]
		> eps        [addToMath(_val)];

	def = lit("definition")
		> id         [_val = new_<Def>(qi::labels::_1)]
		> lit("(")   [pushVars(phoenix::ref(var_stack))]
		> - vars     [phoenix::at_c<0>(*_val) = qi::labels::_1]
		> ")"
		> - disj     [phoenix::at_c<1>(*_val) = qi::labels::_1]
		> "{"
		> - ( + (hyp [push_back(phoenix::at_c<2>(*_val), qi::labels::_1)]) )
		> "defiendum" > ":"
		> id         [_a = qi::labels::_1]
		> "=" > "#"
		> expr(_a)   [phoenix::at_c<3>(*_val) = qi::labels::_1]
		> END_MARKER
		> "definiens" > ":"
		> id         [_a = qi::labels::_1]
		> "=" > "#"
		> expr(_a)   [phoenix::at_c<4>(*_val) = qi::labels::_1]
		> END_MARKER
		> bar
		> "prop" > ":"
		> id         [_a = qi::labels::_1]
		> "=" > "|-"
		> plain(_a)  [phoenix::at_c<5>(*_val) = qi::labels::_1]
		> END_MARKER
		> eps        [assembleDef(_val, phoenix::ref(var_stack))]
		> lit("}")   [pushVars(phoenix::ref(var_stack))]
		> eps        [addToMath(_val)];


	rule =
		lit("rule")
		> - id       [_a = qi::labels::_1]
		> lit("(")   [pushVars(phoenix::ref(var_stack))]
		> - vars     [_b = qi::labels::_1]
		> ")" > "{" > "term" > ":"
		> id         [_c = qi::labels::_1]
		> "=" > lit("#")
		> term(_c)   [_d = qi::labels::_1]
		> END_MARKER
		> lit("}")   [_val = new_<Rule>(_a, _b, _d)]
		> eps        [addToMath(_val)]
		> eps        [popVars(phoenix::ref(var_stack))];

	type =
		lit("type")
		> id        [_a = qi::labels::_1]
		> - (lit(":")
			>  id [push_back(_b, qi::labels::_1)] % ","
		)
		> lit(END_MARKER)  [_val = new_<Type>(_a, _b)]
		> eps [addToMath(_val)];

	constant =
		lit("constant") > "{"
		> lit("symbol")  [_b = phoenix::val(Symbol::undef()), _c = phoenix::val(Symbol::undef())]
		> liter          [_a = qi::labels::_1]
		> lit(END_MARKER)
		> -(
			lit("ascii")
			> liter          [_b = qi::labels::_1]
			> lit(END_MARKER)
		)
		> -(
			lit("latex")
			> liter      [_c = qi::labels::_1]
			> lit(END_MARKER)
		)
		> lit("}")      [_val = new_<Const>(_a, _b, _c)];

	import = lit("import") > path [_val = parseImport(qi::labels::_1, phoenix::val(src))] > END_MARKER;

	comment_text %= lexeme[+(unicode::char_ - "*/" - "/*")];
	comment_ml =
		   lit("/*")
		>> *(
			comment_text [_val = new_<Comment>(qi::labels::_1)] |
			comment_ml [appendComment(_val, qi::labels::_1)]
		)
		>> lit("*/");

	comment_sl =
		   lit("//")
		>> lexeme[+(unicode::char_ - "\n")] [_val = new_<Comment>(makeString(qi::labels::_1))];

	comment %= comment_ml | comment_sl;

	source =
		eps [at_c<0>(_val) = new_<Theory>()]
		> +(
			import   [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(qi::labels::_1))] |
			constant [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(qi::labels::_1))] |
			type     [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(qi::labels::_1))] |
			rule     [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(qi::labels::_1))] |
			axiom    [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(qi::labels::_1))] |
			def      [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(qi::labels::_1))] |
			theorem  [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(qi::labels::_1))] |
			proof    [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(qi::labels::_1))] |
			comment  [push_back(at_c<1>(*at_c<0>(_val)), phoenix::construct<Node>(qi::labels::_1))]
		);

	qi::on_success(id,        setToken(_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(term,      setToken(_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(expr,      setToken(_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(plain,     setToken(_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(comment,   setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(import,    setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(constant,  setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(vars,      setToken(_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(disj,      setToken(_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(type,      setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(rule,      setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(hyp,       setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(prop,      setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(ref,       setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(step,      setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(qed,       setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(proof,     setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));

	qi::on_success(axiom,   setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(theorem, setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(def,     setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));

	//qi::on_success(theory, setToken(phoenix::at_c<2>(*_val), qi::labels::_1, qi::labels::_3));

	qi::on_error<qi::fail>(
		source,
		std::cout << phoenix::val("Syntax error. Expecting ") << qi::labels::_4
		<< phoenix::val(" here: \n") << qi::labels::_3 << phoenix::val("\n")
		<< phoenix::val("code: \n") << phoenix::construct<wrapper<>>(qi::labels::_3));
	initNames();
}

}}} //mdl::rus::parser

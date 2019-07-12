#define BOOST_SPIRIT_USE_PHOENIX_V3
#define BOOST_SPIRIT_UNICODE

#include "rus_parser.hpp"

namespace mdl { namespace rus { namespace parser {

Grammar::Grammar(Source* src) : Grammar::base_type(source, "russell") {
	using qi::lit;
	using qi::uint_;
	using qi::lexeme;
	using qi::eps;
	using qi::labels::_val;
	using qi::labels::_r1;
	using qi::labels::_r2;
	using qi::labels::_r3;
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
	const phoenix::function<ParseExpr>   parseExpr;
	const phoenix::function<ParsePlain>  parsePlain;
	const phoenix::function<ParseTerm>   parseTerm;

	const phoenix::function<PushVars>    pushVars;
	const phoenix::function<PopVars>     popVars;
	const phoenix::function<AddVars>     addVars;
	const phoenix::function<AddVar>      addVar;
	const phoenix::function<SetType>     setType;

	const phoenix::function<CreateStepRef> createStepRef;
	const phoenix::function<GetProp>     getProp;
	const phoenix::function<GetStep>     getStep;

	const phoenix::function<AddDisjVar>  addDisjVar;
	const phoenix::function<NewDisjSet>  newDisjSet;

	const phoenix::function<Enqueue>        enqueue;
	const phoenix::function<ParseImport>    parseImport;
	const phoenix::function<AssembleDef>    assembleDef;
	const phoenix::function<SetToken>       setToken;
	const phoenix::function<MakeString>     makeString;
	const phoenix::function<AppendComment>  appendComment;
	const phoenix::function<AddProofElem>   addProofElem;
	const phoenix::function<AddStepRefs>    addStepRefs;
	const phoenix::function<AddToAssertion> addToAssertion;
	const phoenix::function<AddToTheory>    addToTheory;

	bar   = lexeme[lit("-----")] >> * unicode::char_('-');
	liter = lexeme[+(unicode::char_ - END_MARKER - unicode::space)] [_val = symbToInt(qi::labels::_1)];
	var   = lexeme[+(unicode::char_ - END_MARKER - unicode::space - unicode::char_("),"))] [_val = symbToInt(qi::labels::_1)];
	symb  = lexeme[+(unicode::char_ - END_MARKER - unicode::space)] [_val = symbToInt(qi::labels::_1)];
	id    = lexeme[+ unicode::char_("a-zA-Z0-9_.\\-")]              [_val = idToInt(qi::labels::_1)];
	path  = lexeme[+(unicode::char_ - END_MARKER - unicode::space)];

	term  = + (symb [push_back(_a, qi::labels::_1)] | comment [delete_(qi::labels::_1)]) > eps [parseTerm(_r3, _a, _r2, _r1, phoenix::ref(var_stack)), _val = &_r3];
	expr  = + (symb [push_back(_a, qi::labels::_1)] | comment [delete_(qi::labels::_1)]) > eps [parseExpr(_r2, _a, _r1, phoenix::ref(var_stack)), _val = &_r2];
	plain = + (symb [push_back(_a, qi::labels::_1)] | comment [delete_(qi::labels::_1)]) > eps [parsePlain(_r2, _a, _r1), _val = &_r2];

	disj =
		lit("disjointed") > "("
		> + ( (!(lit(")") | lit(",")))
			> eps    [newDisjSet(_a)]
			> + var  [addDisjVar(_r1, _a, qi::labels::_1)]
		) % ","
		> lit(")") [_val = &_r1];

	vars =
		( !lit(")")
		> var        [_a = qi::labels::_1]
		> ":" > id   [_b = qi::labels::_1]
		> eps        [addVar(phoenix::at_c<0>(_r1), _a, _b)]
		) % ","
		> eps        [addVars(phoenix::ref(var_stack), _r1), _val = &_r1];

	prop =
		lit("prop")
		> - uint_    [_val = new_<Prop>(qi::labels::_1 - 1)]
		> ":"
		> id         [_a = qi::labels::_1]
		> "=" > "|-" > expr(_a, phoenix::at_c<1>(*_val))
		> lit(END_MARKER);

	hyp =
		lit("hyp")
		> - uint_    [_val = new_<Hyp>(qi::labels::_1 - 1)]
		> ":"
		> id         [_a = qi::labels::_1]
		> "=" > "|-" > expr(_a, phoenix::at_c<1>(*_val))
		> lit(END_MARKER);

	ref =
		("hyp"  > uint_ [_val = createStepRef(qi::labels::_1 - 1, _r1, val(Ref::HYP))])  |
		("prop" > uint_ [_val = createStepRef(qi::labels::_1 - 1, _r1, val(Ref::PROP))]) |
		("step" > uint_ [_val = createStepRef(qi::labels::_1 - 1, _r1, val(Ref::STEP))]);

	refs =
		lit("(") > - (ref(_r1) [push_back(_val, qi::labels::_1)] % ",") > ")";

	step =
		lit("step")
		> uint_ [_a = qi::labels::_1 - 1] > ":" > id [_b = qi::labels::_1] > "="
		> (
			(lit("claim") [_c = val(Step::CLAIM), _d = val(Id())]) |
			(lit("?")     [_c = val(Step::CLAIM) ,_d = val(Id())]) |
			(id           [_c = val(Step::ASS),   _d = qi::labels::_1])
		)
		> eps [_val = new_<Step>(_a, _c, _d, _r1)]
		> refs(_r1) [addStepRefs(_val, qi::labels::_1)]
		> lit("|-") [addProofElem(_r1, _val)]
		> expr(_b, phoenix::at_c<1>(*_val))
		> lit(END_MARKER);

	qed =
		lit("qed")
		> lit("prop")   [_val = new_<Qed>()]
		> eps         [_a =  0]
		> - uint_     [_a = qi::labels::_1]
		> lit("=")    [phoenix::at_c<0>(*_val) = getProp(_a - 1, _r1)]
		> lit("step") [addProofElem(_r1, _val)]
		> uint_       [phoenix::at_c<1>(*_val) = getStep(qi::labels::_1 - 1, _r1)]
		> END_MARKER;

	proof_elem = (step(_r1) | qed(_r1));

	proof_body =
		lit("{")   [pushVars(phoenix::ref(var_stack))]
		> - ("var" > vars(phoenix::at_c<1>(*_r1)) > lit(END_MARKER))
		> + proof_elem(_r1)
		> lit("}") [popVars(phoenix::ref(var_stack))];

	proof =
		lit("proof") [_val = new_<Proof>(_r1)]
		> eps        [pushVars(phoenix::ref(var_stack))]
		> eps        [addVars(phoenix::ref(var_stack), phoenix::at_c<3>(*_val))]
		> proof_body(_val)
		> eps        [popVars(phoenix::ref(var_stack))]
		> eps        [enqueue(_val)];

	theorem =
		lit("theorem")
		> id         [_val = new_<Theorem>(qi::labels::_1)]
		> lit("(")   [pushVars(phoenix::ref(var_stack))]
		> - vars(phoenix::at_c<0>(*_val))
		> lit(")") > - disj(phoenix::at_c<1>(*_val)) > "{"
		> - ( + (hyp [addToAssertion(_val, qi::labels::_1)]) > bar )
		> + (prop    [addToAssertion(_val, qi::labels::_1)])
		> lit("}")   [popVars(phoenix::ref(var_stack))]
		> proof(_val) [addToAssertion(_val, qi::labels::_1)]
		> eps        [enqueue(_val)];

	axiom =
		lit("axiom")
		> id         [_val = new_<Axiom>(qi::labels::_1)]
		> lit("(")   [pushVars(phoenix::ref(var_stack))]
		> - vars(phoenix::at_c<0>(*_val))
		> lit(")") > - disj(phoenix::at_c<1>(*_val)) > "{"
		> - ( + (hyp [addToAssertion(_val, qi::labels::_1)]) > bar )
		> + (prop    [addToAssertion(_val, qi::labels::_1)])
		> lit("}")   [popVars(phoenix::ref(var_stack))]
		> eps        [enqueue(_val)];

	def = lit("definition")
		> id         [_val = new_<Def>(qi::labels::_1)]
		> lit("(")   [pushVars(phoenix::ref(var_stack))]
		> - vars(phoenix::at_c<0>(*_val))
		> lit(")") > - disj(phoenix::at_c<1>(*_val)) > "{"
		> - ( + (hyp [addToAssertion(_val, qi::labels::_1)]) )
		> "defiendum" > ":"
		> id         [_a = qi::labels::_1]
		> "=" > "#" > expr(_a, phoenix::at_c<3>(*_val)) > END_MARKER
		> "definiens" > ":"
		> id         [_a = qi::labels::_1]
		> "=" > "#" > expr(_a, phoenix::at_c<4>(*_val)) > END_MARKER
		> bar
		> "prop" > ":"
		> id         [_a = qi::labels::_1]
		> "=" > "|-" > plain(_a, phoenix::at_c<5>(*_val)) > END_MARKER
		> eps        [assembleDef(_val, phoenix::ref(var_stack))]
		> lit("}")   [pushVars(phoenix::ref(var_stack))]
		> eps        [enqueue(_val)];

	rule =
		lit("rule")
		> - id       [_a = qi::labels::_1, _val = new_<Rule>(_a)]
		> lit("(")   [pushVars(phoenix::ref(var_stack))]
		> - vars(phoenix::at_c<1>(*_val)) > ")" > "{"
		> "term" > ":"
		> id         [_b = qi::labels::_1]
		> "=" > lit("#")
		> term(_b, _a, phoenix::at_c<2>(*_val)) > END_MARKER
		> lit("}")   [popVars(phoenix::ref(var_stack))];

	type =
		lit("type")
		> id        [_a = qi::labels::_1]
		> - (lit(":")
			>  id [push_back(_b, qi::labels::_1)] % ","
		)
		> lit(END_MARKER)  [_val = new_<Type>(_a, _b)];

	constant =
		lit("constant") > "{"
		> lit("symbol")  [_b = phoenix::val(-1), _c = phoenix::val(-1)]
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
		> lit("}")      [_val = new_<Constant>(_a, _b, _c)];

	import = lit("import") > path [_val = parseImport(qi::labels::_1, phoenix::val(src))] > END_MARKER;

	comment_text %= lexeme[+(unicode::char_ - "*/" - "/*")];
	comment_ml =
		   lit("/*") [_val = new_<Comment>(phoenix::val(true))]
		>> *(
			comment_text [appendComment(_val, qi::labels::_1)] |
			comment_ml [appendComment(_val, qi::labels::_1)]
		)
		>> lit("*/");

	comment_sl =
		   lit("//")
		>> lexeme[+(unicode::char_ - "\n")] [_val = new_<Comment>(phoenix::val(false), makeString(qi::labels::_1))];

	comment %= comment_ml | comment_sl;

	source =
		+(
			import   [addToTheory(&at_c<0>(*_val), qi::labels::_1)] |
			constant [addToTheory(&at_c<0>(*_val), qi::labels::_1)] |
			type     [addToTheory(&at_c<0>(*_val), qi::labels::_1)] |
			rule     [addToTheory(&at_c<0>(*_val), qi::labels::_1)] |
			axiom    [addToTheory(&at_c<0>(*_val), qi::labels::_1)] |
			def      [addToTheory(&at_c<0>(*_val), qi::labels::_1)] |
			theorem  [addToTheory(&at_c<0>(*_val), qi::labels::_1)] |
			comment  [addToTheory(&at_c<0>(*_val), qi::labels::_1)]
		);

	//qi::on_success(id,        setToken(_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(term,      setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(expr,      setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(plain,     setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(comment,   setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(import,    setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(constant,  setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(vars,      setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
	qi::on_success(disj,      setToken(*_val, qi::labels::_1, qi::labels::_3, phoenix::val(src)));
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

} // parser namespace

#ifdef PARALLEL
#define PARALLEL_RUS_PARSE
#endif

void parse_src_spirit(uint label) {
	Source* src = Sys::mod().math.get<Source>().access(label);

	LocationIter iter(src->data().begin(), label);
	LocationIter end(src->data().end(), label);
	parser::Grammar grammar(src);

	if (!parser::qi::phrase_parse(iter, end, grammar, parser::unicode::space, src)|| iter != end) {
		throw Error("parsing failed", Lex::toStr(label));
	}
	src->parsed = true;
}

void parse_src_spirit() {
	vector<uint> labels;
	for (auto p : Sys::mod().math.get<Source>()) {
		if (!p.second.data->parsed) {
			labels.push_back(p.first);
		}
	}
#ifdef PARALLEL_RUS_PARSE
	tbb::parallel_for (tbb::blocked_range<size_t>(0, labels.size()),
		[labels] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i)
				parse_src_spirit(labels[i]);
		}
	);
#else
	for (auto src : labels) {
		parse_src_spirit(src);
	}
#endif
}

}} // mdl::rus

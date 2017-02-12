#define BOOST_RESULT_OF_USE_DECLTYPE
#define BOOST_SPIRIT_USE_PHOENIX_V3

#include "spirit_parser.hpp"

namespace mdl { namespace mm { namespace parser {

Grammar::Grammar(Context& context) : Grammar::base_type(source, "mm") {
	using qi::lit;
	using qi::uint_;
	using qi::lexeme;
	using qi::eps;
	using namespace qi::labels;
	using phoenix::at_c;
	using phoenix::push_back;
	using phoenix::new_;
	using phoenix::delete_;

	const phoenix::function<CreateLabel>    createLabel;
	const phoenix::function<CreateSymb>     createSymb;
	const phoenix::function<ParseInclusion> parseInclusion;
	const phoenix::function<AddVars>        addVars;
	const phoenix::function<AddConsts>      addConsts;
	const phoenix::function<MarkVars>       markVars;
	const phoenix::function<MakeString>     makeString;

	const bool is_top = context.stack.empty();
	//const phoenix::function<SetLocation<Iterator>> setLocation;

	symbol = lexeme[+(ascii::char_ - '$' - ascii::space)] [_val = createSymb(_1)];
	label  = lexeme[+(ascii::char_ - '$' - ascii::space)] [_val = createLabel(_1)];
	path   = lexeme[+(ascii::char_ - '$' - ascii::space)];

	expr  = + (symbol [push_back(_val, _1)] | comment [delete_(_1)]);

	ref   = label   [_val = new_<mm::Ref>(_1)];
	proof =
		eps         [_val = new_<mm::Proof>()]
		> +ref      [push_back(phoenix::at_c<0>(*_val), _1)]
		> "$.";
	theorem =
		  label     [_a = _1]
		>> lit("$p")
		> expr      [_b = _1]
		> eps       [markVars(_b, phoenix::ref(context.stack))]
		> lit("$=")
		> proof     [_c = _1]
		> eps       [_val = new_<mm::Theorem>(_a, _b, _c)];
	axiom =
		   label    [_a = _1]
		>> lit("$a")
		> expr      [_b = _1]
		> eps       [markVars(_b, phoenix::ref(context.stack))]
		> lit("$.") [_val = new_<mm::Axiom>(_a, _b)];
	essential =
		  label     [_a = _1]
		>> lit("$e")
		> expr      [_b = _1]
		> eps       [markVars(_b, phoenix::ref(context.stack))]
		> lit("$.") [_val = new_<mm::Essential>(_a, _b)];
	floating =
		  label     [_a = _1]
		>> lit("$f")
		> expr      [_b = _1]
		> eps       [markVars(_b, phoenix::ref(context.stack))]
		> lit("$.") [_val = new_<mm::Floating>(_a, _b)];
	disjointed =
		lit("$d")   [_val = new_<mm::Disjointed>()]
		> expr      [phoenix::at_c<0>(*_val) = _1]
		> eps       [markVars(phoenix::at_c<0>(*_val), phoenix::ref(context.stack))]
		> "$.";
	variables =
		lit("$v")   [_val = new_<mm::Variables>()]
		> expr      [phoenix::at_c<0>(*_val) = _1]
		> lit("$.") [addVars(phoenix::ref(context.stack), phoenix::at_c<0>(*_val))];
	constants =
		lit("$c")   [_val = new_<mm::Constants>()]
		> expr      [phoenix::at_c<0>(*_val) = _1]
		> lit("$.") [addConsts(phoenix::ref(context.stack), phoenix::at_c<0>(*_val))];
	inclusion = lit("$[") > path [_val = parseInclusion(_1, phoenix::ref(context))] > "$]";
	comment =
		lit("$(") >> lexeme[*(ascii::char_ - "$)")] [_val = new_<mm::Comment>(makeString(_1))] >> "$)";
	node %= (
		constants  |
		variables  |
		disjointed |
		block      |
		floating   |
		essential  |
		axiom      |
		theorem    );

	const phoenix::function<PushParent> pushParent;
	const phoenix::function<PopParent>  popParent;
	const phoenix::function<PushNode>   pushNode;
	const phoenix::function<PushVC>     pushVC;
	const phoenix::function<PopVC>      popVC;

	block =
		lit("${")   [_val = new_<mm::Block>(phoenix::val(context.parent))]
		> eps       [pushParent(_val, phoenix::ref(context.parent))]
		> eps       [pushVC(phoenix::ref(context.stack), phoenix::val(true))]
		> * (
			comment [pushNode(_val, _1)] |
			node    [pushNode(_val, _1)]
		)
		> lit("$}") [popParent(_val, phoenix::ref(context.parent))]
		> eps       [popVC(phoenix::ref(context.stack), phoenix::val(true))];

	source =
		  eps       [phoenix::at_c<1>(*phoenix::at_c<2>(_val)) = phoenix::val(context.parent)]
		> eps       [pushVC(phoenix::ref(context.stack), phoenix::val(is_top))]
		> eps       [pushParent(phoenix::at_c<2>(_val), phoenix::ref(context.parent))]
		> * (
			comment   [pushNode(phoenix::at_c<2>(_val), _1)] |
			node      [pushNode(phoenix::at_c<2>(_val), _1)] |
			inclusion [pushNode(phoenix::at_c<2>(_val), _1)]
		)
		> eps       [popParent(phoenix::at_c<2>(_val), phoenix::ref(context.parent))]
		> eps       [popVC(phoenix::ref(context.stack), phoenix::val(is_top))];

	//qi::on_success(assertion, setLocation(_val, _1));
	qi::on_error<qi::fail>(
		source,
		std::cout << phoenix::val("Syntax error. Expecting ") << _4
		<< phoenix::val(" here: \n") << _3 << phoenix::val("\n")
		<< phoenix::val("code: \n") <<phoenix::construct<wrapper<>>(_3));
	initNames();
}

} // parser

void spirit_parse(uint label) {
	parser::Context context;
	parser::Grammar::parse(label, context);
}

}} // mdl::mm

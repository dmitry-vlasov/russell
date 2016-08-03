#define BOOST_SPIRIT_USE_PHOENIX_V3

#include "mm/parser.hpp"

namespace mdl { namespace mm { namespace parser {

template <typename Iterator>
Grammar<Iterator>::Grammar() : Grammar::base_type(source, "russell") {
		using qi::lit;
		using qi::uint_;
		using qi::lexeme;
		using qi::eps;
		using namespace qi::labels;
		using phoenix::at_c;
		using phoenix::push_back;
		using phoenix::new_;

		const phoenix::function<LabelToInt>     labelToInt;
		const phoenix::function<SymbolToInt>    symbolToInt;
		const phoenix::function<AddToMath>      addToMath;
		const phoenix::function<ParseInclusion> parseInclusion;
		const phoenix::function<CreateRef>      createRef;
		const phoenix::function<AddVars>        addVars;
		const phoenix::function<AddConsts>      addConsts;
		const phoenix::function<MarkVars>       markVars;
		const phoenix::function<MakeString>     makeString;

		static Stack  stack;
		static Block* parent = nullptr;
		const bool is_top = stack.empty();
		//const phoenix::function<SetLocation<Iterator>> setLocation;

		symbol = lexeme[+(ascii::char_ - '$' - ascii::space)] [at_c<0>(_val) = symbolToInt(_1)];
		label  = lexeme[+(ascii::char_ - '$' - ascii::space)] [_val = labelToInt(_1)];
		path   = lexeme[+(ascii::char_ - '$' - ascii::space)];

		expr  = + (symbol [push_back(at_c<0>(_val), _1)] | comment);

		ref   = label   [_val = createRef(_1)];
		proof =
			eps         [_val = new_<mm::Proof>()]
			> +ref      [push_back(phoenix::at_c<0>(*_val), _1)]
			> "$.";
		theorem =
			  label     [_a = _1]
			>> lit("$p")[_val = new_<mm::Theorem>()]
			> eps       [phoenix::at_c<0>(*_val) = _a]
			> expr      [phoenix::at_c<1>(*_val) = _1]
			> eps       [markVars(phoenix::at_c<1>(*_val), phoenix::ref(stack))]
			> lit("$=") [addToMath(_val)]
			> proof     [phoenix::at_c<3>(*_val) = _1];
		axiom =
			   label    [_a = _1]
			>> lit("$a")[_val = new_<mm::Axiom>()]
			> eps       [phoenix::at_c<0>(*_val) = _a]
			> expr      [phoenix::at_c<1>(*_val) = _1]
			> eps       [markVars(phoenix::at_c<1>(*_val), phoenix::ref(stack))]
			> lit("$.") [addToMath(_val)];
		essential =
			  label     [_a = _1]
			>> lit("$e")[_val = new_<mm::Essential>()]
			> eps       [phoenix::at_c<0>(*_val) = _a]
			> expr      [phoenix::at_c<1>(*_val) = _1]
			> eps       [markVars(phoenix::at_c<1>(*_val), phoenix::ref(stack))]
			> lit("$.") [addToMath(_val)];
		floating =
			  label     [_a = _1]
			>> lit("$f")[_val = new_<mm::Floating>()]
			> eps       [phoenix::at_c<0>(*_val) = _a]
			> expr      [phoenix::at_c<1>(*_val) = _1]
			> eps       [markVars(phoenix::at_c<1>(*_val), phoenix::ref(stack))]
			> lit("$.") [addToMath(_val)];
		disjointed =
			lit("$d")   [_val = new_<mm::Disjointed>()]
			> expr      [phoenix::at_c<0>(*_val) = _1]
			> eps       [markVars(phoenix::at_c<0>(*_val), phoenix::ref(stack))]
			> "$.";
		variables =
			lit("$v")   [_val = new_<mm::Variables>()]
			> expr      [phoenix::at_c<0>(*_val) = _1]
			> lit("$.") [addVars(phoenix::ref(stack), phoenix::at_c<0>(*_val))];
		constants =
			lit("$c")   [_val = new_<mm::Constants>()]
			> expr      [phoenix::at_c<0>(*_val) = _1]
			> lit("$.") [addConsts(phoenix::ref(stack), phoenix::at_c<0>(*_val))];
		inclusion = lit("$[") > path [_val = parseInclusion(_1)] > "$]";
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
			lit("${")   [_val = new_<mm::Block>(phoenix::val(parent))]
			> eps       [pushParent(_val, phoenix::ref(parent))]
			> eps       [pushVC(phoenix::ref(stack), phoenix::val(true))]
			> * (
				comment [pushNode(_val, _1)] |
				node    [pushNode(_val, _1)]
			)
			> lit("$}") [popParent(_val, phoenix::ref(parent))]
			> eps       [popVC(phoenix::ref(stack), phoenix::val(true))];

		source =
			  eps       [phoenix::at_c<1>(*phoenix::at_c<2>(_val)) = phoenix::val(parent)]
			> eps       [pushVC(phoenix::ref(stack), phoenix::val(is_top))]
			> eps       [pushParent(phoenix::at_c<2>(_val), phoenix::ref(parent))]
			> * (
				comment   [pushNode(phoenix::at_c<2>(_val), _1)] |
				node      [pushNode(phoenix::at_c<2>(_val), _1)] |
				inclusion [pushNode(phoenix::at_c<2>(_val), _1)]
			)
			> eps       [popParent(phoenix::at_c<2>(_val), phoenix::ref(parent))]
			> eps       [popVC(phoenix::ref(stack), phoenix::val(is_top))];

		//qi::on_success(assertion, setLocation(_val, _1));
		qi::on_error<qi::fail>(
			source,
			std::cout << phoenix::val("Syntax error. Expecting ") << _4
			<< phoenix::val(" here: \n") << _3 << phoenix::val("\n")
			<< phoenix::val("code: \n") <<phoenix::construct<wrapper<>>(_3));
		initNames();
	}

}}} // mdl::mm::parser

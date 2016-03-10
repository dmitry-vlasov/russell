#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "mm/ast.hpp"
#include "mm/globals.hpp"
#include "mm/adaptors.hpp"

namespace mdl { namespace mm {

namespace qi = boost::spirit::qi;
namespace ascii = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

struct AddToMath {
	template<typename T>
	struct result { typedef void type; };
	void operator()(Floating* flo) const {
		Mm::mod().math.floatings[flo->label] = flo;
	}
	void operator()(Essential* ess) const {
		Mm::mod().math.essentials[ess->label] = ess;
	}
	void operator()(Axiom* ax) const {
		Mm::mod().math.axioms[ax->label] = ax;
	}
	void operator()(Theorem* th) const {
		Mm::mod().math.theorems[th->label] = th;
	}
};

struct SymbolToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<char>& symb) const {
		std::string symbol(symb.begin(), symb.end());
		return Mm::mod().lex.symbols.toInt(symbol);
	}
};

struct LabelToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<char>& lab) const {
		std::string label(lab.begin(), lab.end());
		return Mm::mod().lex.labels.toInt(label);
	}
};

static Block* source(const string& path);

struct ParseInclusion {
	template <typename T>
	struct result { typedef Block* type; };
	Block* operator()(const string& path) const {
		return source(path);
	}
};

struct CreateRef {
	template <typename T>
	struct result { typedef Node type; };
	Node operator()(uint lab) const {
		Mm::Math& math = Mm::mod().math;
		if (math.floatings.has(lab))
			return Node(math.floatings[lab]);
		else if (math.essentials.has(lab))
			return Node(math.essentials[lab]);
		else if (math.axioms.has(lab))
			return Node(math.axioms[lab]);
		else if (math.theorems.has(lab))
			return Node(math.theorems[lab]);
		else
			return Node();
			//throw Error("unknown label in proof", Mm::get().lex.labels.toStr(lab));
	}
};

/*
template<typename Iterator>
struct SetLocation {
    template <typename T1, typename T2>
    struct result { typedef void type; };
    void operator()(Assertion* ass, Iterator it) const {
    	ass->loc = it.loc;
    }
};
*/
template <typename Iterator>
struct Grammar : qi::grammar<Iterator, Block(), ascii::space_type> {
	Grammar() : Grammar::base_type(source, "russell") {
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
		//const phoenix::function<SetLocation<Iterator>> setLocation;

		symbol = lexeme[+(ascii::char_ - '$' - ascii::space)] [at_c<0>(_val) = symbolToInt(_1)];
		label  = lexeme[+(ascii::char_ - '$' - ascii::space)] [_val = labelToInt(_1)];
		path   = lexeme[+(ascii::char_ - '$' - ascii::space)];

		expr = +symbol [push_back(at_c<0>(_val), _1)];

		ref  = label    [phoenix::at_c<0>(_val) = createRef(_1)];
		proof =
			eps         [_val = new_<mm::Proof>()]
			> +ref      [push_back(phoenix::at_c<0>(*_val), _1)]
			> "$.";
		theorem =
			eps         [_val = new_<mm::Theorem>()]
			>> label    [phoenix::at_c<0>(*_val) = _1]
			>> "$p"
			> expr      [phoenix::at_c<1>(*_val) = _1]
			> lit("$=") [addToMath(_val)]
			> proof     [phoenix::at_c<2>(*_val) = _1];
		axiom =
			eps         [_val = new_<mm::Axiom>()]
			>> label    [phoenix::at_c<0>(*_val) = _1]
			>> "$a"
			> expr      [phoenix::at_c<1>(*_val) = _1]
			> lit("$.") [addToMath(_val)];
		essential =
			eps         [_val = new_<mm::Essential>()]
			>> label    [phoenix::at_c<0>(*_val) = _1]
			>> "$e"
			> expr      [phoenix::at_c<1>(*_val) = _1]
			> lit("$.") [addToMath(_val)];
		floating =
			eps         [_val = new_<mm::Floating>()]
			>> label    [phoenix::at_c<0>(*_val) = _1]
			>> "$f"
			> expr      [phoenix::at_c<1>(*_val) = _1]
			> lit("$.") [addToMath(_val)];
		disjointed =
			lit("$d")   [_val = new_<mm::Disjointed>()]
			> expr      [phoenix::at_c<0>(*_val) = _1]
			> "$.";
		variables =
			lit("$v")   [_val = new_<mm::Variables>()]
			> expr      [phoenix::at_c<0>(*_val) = _1]
			> "$.";
		constants =
			lit("$c")   [_val = new_<mm::Constants>()]
			> expr      [phoenix::at_c<0>(*_val) = _1]
			> "$.";
		inclusion = lit("$[") > path [_val = parseInclusion(_1)] > "$]";
		comment = lit("$(") >> lexeme[*(ascii::char_ - "$)")] >> "$)";
		node %= (
			constants  |
			variables  |
			disjointed |
			block      |
			floating   |
			essential  |
			axiom      |
			theorem    );
		block =
			lit("${") [_val = new_<mm::Block>()]
			> + (
				comment |
				node  [push_back(phoenix::at_c<2>(*_val), _1)])
			> "$}";
		source = +(
			comment |
			node      [push_back(phoenix::at_c<2>(_val), _1)] |
			inclusion [push_back(phoenix::at_c<2>(_val), phoenix::construct<Node>(_1))]);

		//qi::on_success(assertion, setLocation(_val, _1));
		qi::on_error<qi::fail>(
			source,
			std::cout << phoenix::val("Syntax error. Expecting ") << _4 << phoenix::val(" here: \n") << _3);
		initNames();
	}
	void initNames();

	qi::rule<Iterator, Expr(), ascii::space_type> expr;
	qi::rule<Iterator, Symbol(), ascii::space_type> symbol;
	qi::rule<Iterator, uint(),        ascii::space_type> label;
	qi::rule<Iterator, std::string(), ascii::space_type> path;
	qi::rule<Iterator, Ref(), ascii::space_type> ref;
	qi::rule<Iterator, Proof*(), ascii::space_type> proof;
	qi::rule<Iterator, Essential*(), ascii::space_type> essential;
	qi::rule<Iterator, Floating*(), ascii::space_type> floating;
	qi::rule<Iterator, Disjointed*(), ascii::space_type> disjointed;
	qi::rule<Iterator, Variables*(), ascii::space_type> variables;
	qi::rule<Iterator, Axiom*(), ascii::space_type> axiom;
	qi::rule<Iterator, Theorem*(), ascii::space_type> theorem;
	qi::rule<Iterator, Constants*(), ascii::space_type> constants;
	qi::rule<Iterator, Node(), ascii::space_type> node;
	qi::rule<Iterator, Block*(), ascii::space_type> block;
	qi::rule<Iterator, Block*(), ascii::space_type> inclusion;
	qi::rule<Iterator, qi::unused_type, ascii::space_type> comment;
	qi::rule<Iterator, Block(), ascii::space_type> source;
};

template <typename Iterator>
void Grammar<Iterator>::initNames() {
	symbol.name("symbol");
	label.name("label");
	path.name("path");
	expr.name("expr");
	ref.name("ref");
	proof.name("proof");
	theorem.name("theorem");
	axiom.name("axiom");
	essential.name("essential");
	floating.name("floating");
	disjointed.name("disjointed");
	variables.name("variables");
	node.name("node");
	block.name("block");
	constants.name("constants");
	comment.name("name");
	inclusion.name("inclusion");
	source.name("source");
}

static Block* source(const string& path) {
	ifstream in(path, std::ios_base::in);
	if (!in)
		throw Error("Could not open input file");

	string storage;
	in.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(in),
		std::istream_iterator<char>(),
		std::back_inserter(storage));

	LocationIter iter(storage.begin(), path);
	LocationIter end(storage.end(), path);
	Block* source = new Block(path);
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, *source);
	if (!r || iter != end) {
		throw Error("parsing failed");
	}
	return source;
}

Block* parse(const string& path) {
	return source(path);
}

}} // mdl::mm

#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "smm/ast.hpp"
#include "smm/globals.hpp"
#include "smm/adaptors.hpp"

namespace mdl { namespace smm { namespace parse1 {

namespace qi = boost::spirit::qi;
namespace ascii = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

class LocationIter : public string::const_iterator {
	void inc(char ch) {
		if (ch == '\n') {
			loc.col = 0;
			++ loc.line;
		} else
			++ loc.col;
	}
public:
	LocationIter(const LocationIter& it) :
	string::const_iterator(it), loc(it.loc) { }
	LocationIter(string::const_iterator it, const string& file) :
	string::const_iterator(it), loc(file) { }

	LocationIter& operator ++() {
		inc(*string::const_iterator::operator++());
		return *this;
	}
	LocationIter operator ++(int) {
		LocationIter curr(*this);
		inc(*string::const_iterator::operator++());
		return curr;
	}
	Location loc;
};

std::ostream& operator << (std::ostream& os, const LocationIter& it){
	os << show(it.loc);
	return os;
}

inline void makeVars(Expr& expr) {
	for (auto v_it = expr.symbols.begin(); v_it != expr.symbols.end(); ++ v_it)
		v_it->isVar = true;
}

template<typename T>
inline void makeVars(vector<T>& vars) {
	for (auto v_it = vars.begin(); v_it != vars.end(); ++ v_it)
		makeVars(v_it->expr);
}

static void markVars(const vector<Variables>& vars, Expr& expr) {
	for (auto v_it = vars.cbegin(); v_it != vars.cend(); ++ v_it) {
		expr.markVars(v_it->expr);
	}
}

template<class T>
static void markVars(const vector<Variables>& vars, vector<T>& components) {
	for (auto ex_it = components.begin(); ex_it != components.end(); ++ ex_it) {
		markVars(vars, ex_it->expr);
	}
}

struct AddToMath {
	template<typename T>
	struct result { typedef void type; };
	void operator()(Assertion* ass) const {
		makeVars(ass->variables);
		makeVars(ass->disjointed);
		markVars(ass->variables, ass->floating);
		markVars(ass->variables, ass->inner);
		markVars(ass->variables, ass->essential);
		markVars(ass->variables, ass->prop.expr);
		Smm::mod().math.assertions.push_back(ass);
	}
	void operator()(Constants* c) const {
		for (auto it = c->expr.symbols.begin(); it != c->expr.symbols.end(); ++ it)
			Smm::mod().math.constants.insert(*it);
	}
};

struct SymbolToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<char>& symb) const {
		std::string symbol(symb.begin(), symb.end());
		return Smm::mod().lex.symbols.toInt(symbol);
	}
};

struct LabelToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<char>& lab) const {
		std::string label(lab.begin(), lab.end());
		return Smm::mod().lex.labels.toInt(label);
	}
};

struct ParseInclusion {
	template <typename T>
	struct result { typedef Source* type; };
	Source* operator()(const string& path) const {
		return source(path);
	}
};

template<typename Iterator>
struct SetLocation {
    template <typename T1, typename T2>
    struct result { typedef void type; };
    void operator()(Assertion* ass, Iterator it) const {
    	ass->loc = it.loc;
    }
};

template <typename Iterator>
struct Grammar : qi::grammar<Iterator, smm::Source(), ascii::space_type> {
	Grammar() : Grammar::base_type(source, "russell") {
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

		symbol = lexeme[+(ascii::char_ - '$' - ' ')] [at_c<0>(_val) = symbolToInt(_1)];
		label  = lexeme[+(ascii::char_ - '$' - ' ')] [_val = labelToInt(_1)];
		path   = lexeme[+(ascii::char_ - '$' - ' ')];

		expr_e = + symbol [push_back(at_c<0>(_val), _1)] > "$.";
		expr_p = + symbol [push_back(at_c<0>(_val), _1)] > "$=";
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
			qi::eps [_val = new_<smm::Proof>()]
			> +(a_ref | p_ref | e_ref | f_ref | i_ref) [push_back(phoenix::at_c<0>(*_val), _1)]
			> "$.";
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
				> proof      [phoenix::at_c<6>(*_val) = _1])
			)
			> lit("$}")      [addToMath(_val)];
		constants =
			lit("$c") [_val = new_<smm::Constants>()]
			> expr_e  [phoenix::at_c<0>(*_val) = _1]
			> qi::eps [addToMath(_val)];
		inclusion = lit("$[")
			> path [_val = parseInclusion(_1)]
			> "$]";
		comment = lit("$(") >> lexeme[+(ascii::char_ - '$')] >> "$)";
		source = +(
			constants [push_back(at_c<2>(_val), phoenix::construct<Source::Node>(_1))] |
			assertion [push_back(at_c<2>(_val), phoenix::construct<Source::Node>(_1))] |
			inclusion [push_back(at_c<2>(_val), phoenix::construct<Source::Node>(_1))] |
			comment);

		qi::on_success(assertion, setLocation(_val, _1));
		qi::on_error<qi::fail>(
			source,
			std::cout << phoenix::val("Syntax error. Expecting ") << _4 << phoenix::val(" here: \n") << _3);
		initNames();
	}
	void initNames();

	qi::rule<Iterator, Expr(), ascii::space_type> expr_e;
	qi::rule<Iterator, Expr(), ascii::space_type> expr_f;
	qi::rule<Iterator, Expr(), ascii::space_type> expr_p;
	qi::rule<Iterator, Symbol(), ascii::space_type> symbol;
	qi::rule<Iterator, uint(),        ascii::space_type> label;
	qi::rule<Iterator, std::string(), ascii::space_type> path;
	qi::rule<Iterator, Ref(), ascii::space_type> a_ref;
	qi::rule<Iterator, Ref(), ascii::space_type> p_ref;
	qi::rule<Iterator, Ref(), ascii::space_type> e_ref;
	qi::rule<Iterator, Ref(), ascii::space_type> f_ref;
	qi::rule<Iterator, Ref(), ascii::space_type> i_ref;
	qi::rule<Iterator, Proof*(), ascii::space_type> proof;
	qi::rule<Iterator, Proposition(), ascii::space_type> provable;
	qi::rule<Iterator, Proposition(), ascii::space_type> axiomatic;
	qi::rule<Iterator, Essential(), ascii::space_type> essential;
	qi::rule<Iterator, Floating(), ascii::space_type> floating;
	qi::rule<Iterator, Inner(), ascii::space_type> inner;
	qi::rule<Iterator, Disjointed(), ascii::space_type> disjointed;
	qi::rule<Iterator, Variables(), ascii::space_type> variables;
	qi::rule<Iterator, Assertion*(), ascii::space_type> assertion;
	qi::rule<Iterator, Constants*(), ascii::space_type> constants;
	qi::rule<Iterator, Source*(), ascii::space_type> inclusion;
	qi::rule<Iterator, qi::unused_type, ascii::space_type> comment;
	qi::rule<Iterator, Source(), ascii::space_type> source;
};

template <typename Iterator>
void Grammar<Iterator>::initNames() {
	symbol.name("symbol");
	label.name("label");
	path.name("path");
	a_ref.name("a ref");
	p_ref.name("p ref");
	e_ref.name("e ref");
	f_ref.name("f ref");
	i_ref.name("i ref");
	proof.name("proof");
	provable.name("provable");
	axiomatic.name("axiomatic");
	essential.name("essential");
	floating.name("floating");
	inner.name("inner");
	disjointed.name("disjointed");
	variables.name("variables");
	assertion.name("assertion");
	constants.name("constants");
	comment.name("name");
	inclusion.name("inclusion");
	source.name("source");
}

Source* source(const string& path) {
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
	Source* source = new Source(path);
	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, *source);
	if (!r || iter != end) {
		throw Error("parsing failed");
	}
	return source;
}

}}} // mdl::smm::parser

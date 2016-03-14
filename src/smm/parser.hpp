#define BOOST_SPIRIT_USE_PHOENIX_V3

#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "smm/ast.hpp"
#include "smm/globals.hpp"
#include "smm/adaptors.hpp"

namespace mdl { namespace smm {

namespace qi = boost::spirit::qi;
namespace ascii = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

inline void makeVars(Expr& expr) {
	for (auto& symb : expr.symbols)
		symb.var = true;
}

template<typename T>
inline void makeVars(vector<T>& vars) {
	for (auto& v_it : vars)
		makeVars(v_it.expr);
}

inline void markVars(const vector<Variables>& vars, Expr& expr) {
	for (auto& v_it : vars) {
		expr.markVars(v_it.expr);
	}
}

template<class T>
inline void markVars(const vector<Variables>& vars, vector<T>& components) {
	for (auto& comp : components) {
		markVars(vars, comp.expr);
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
		for (auto symb : c->expr.symbols)
			Smm::mod().math.constants.insert(symb);
	}
};

struct SymbolToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<char>& symb) const {
		string symbol(symb.begin(), symb.end());
		return Smm::mod().lex.symbols.toInt(symbol);
	}
};

struct LabelToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<char>& lab) const {
		string label(lab.begin(), lab.end());
		return Smm::mod().lex.labels.toInt(label);
	}
};

static Source* source(const string& path);

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
	Grammar();
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
	qi::rule<Iterator, Proof*(Assertion*), ascii::space_type> proof;
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
	expr_e.name("expr_e");
	expr_f.name("expr_f");
	expr_p.name("expr_p");
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

}} // mdl::smm

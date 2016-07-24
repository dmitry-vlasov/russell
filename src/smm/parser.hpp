#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "smm/globals.hpp"
#include "smm/adaptors.hpp"

namespace mdl { namespace smm {

namespace qi = boost::spirit::qi;
namespace ascii = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

struct MakeString {
	template <typename T>
	struct result { typedef string type; };
	string operator()(const vector<char>& s) const {
		return string(s.begin(), s.end());
	}
};

inline void makeVars(Expr& expr) {
	for (auto& symb : expr.symbols)
		symb.var = true;
}

template<typename T>
inline void makeVars(vector<T*>& vars) {
	for (auto& v_it : vars)
		makeVars(v_it->expr);
}

inline void markVars(Expr& ex, const Expr& vars) {
	for (auto& s : ex.symbols) {
		if (vars.contains(s.lit))
			s.var = true;
	}
}

inline void markVars(const vector<Variables*>& vars, Expr& expr) {
	for (auto& v_it : vars) {
		markVars(expr, v_it->expr);
	}
}

template<class T>
inline void markVars(const vector<Variables*>& vars, vector<T>& components) {
	for (auto& comp : components) {
		markVars(vars, comp->expr);
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

struct ParseInclusion {
	template <typename T>
	struct result { typedef Inclusion* type; };
	Inclusion* operator()(const string& name) const {
		static Map<string, Inclusion*> included;
		if (included.has(name)) {
			Inclusion* inc = included[name];
			return new Inclusion(inc->source, false);
		} else {
			Inclusion* inc = new Inclusion(parse(name), true);
			included[name] = inc;
			return inc;
		}
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

struct HypRefs : qi::symbols<char, Ref::Type> {
	HypRefs() {
		add
		("e", Ref::ESSENTIAL)
		("f", Ref::FLOATING)
		("i", Ref::INNER);
	}
};

struct PropRefs : qi::symbols<char, Ref::Type> {
	PropRefs() {
		add
		("a", Ref::AXIOM)
		("p", Ref::THEOREM);
	}
};

struct CreateRef {
    template <typename T1, typename T2, typename T3>
    struct result { typedef Ref type; };
    Ref operator()(Ref::Type tp, uint ind, Assertion* ass) const {
    	switch (tp) {
    	case Ref::ESSENTIAL: return Ref(ass->essential[ind]);
    	case Ref::FLOATING:  return Ref(ass->floating[ind]);
    	case Ref::INNER:     return Ref(ass->inner[ind]);
    	case Ref::AXIOM:     return Ref(Smm::get().math.assertions[ind], true);
    	case Ref::THEOREM:   return Ref(Smm::get().math.assertions[ind], false);
    	default : assert(false && "impossible");
    	}
    	return Ref(); // pacifying compiler
    }
};

template <typename Iterator>
struct Grammar : qi::grammar<Iterator, smm::Source(), ascii::space_type> {
	Grammar();
	void initNames();

	PropRefs prop_refs;
	HypRefs  hyp_refs;
	qi::rule<Iterator, Expr(), ascii::space_type> expr;
	qi::rule<Iterator, Symbol(), ascii::space_type> symbol;
	qi::rule<Iterator, uint(),        ascii::space_type> label;
	qi::rule<Iterator, std::string(), ascii::space_type> path;
	qi::rule<Iterator, Ref(Assertion*), qi::locals<Ref::Type>, ascii::space_type> ref;
	qi::rule<Iterator, Proof*(Assertion*), ascii::space_type> proof;
	qi::rule<Iterator, Proposition(), ascii::space_type> provable;
	qi::rule<Iterator, Proposition(), ascii::space_type> axiomatic;
	qi::rule<Iterator, Essential*(), ascii::space_type> essential;
	qi::rule<Iterator, Floating*(), ascii::space_type> floating;
	qi::rule<Iterator, Inner*(), ascii::space_type> inner;
	qi::rule<Iterator, Disjointed*(), ascii::space_type> disjointed;
	qi::rule<Iterator, Variables*(), ascii::space_type> variables;
	qi::rule<Iterator, Assertion*(), ascii::space_type> assertion;
	qi::rule<Iterator, Constants*(), ascii::space_type> constants;
	qi::rule<Iterator, Inclusion*(), ascii::space_type> inclusion;
	qi::rule<Iterator, Comment*(), ascii::space_type> comment;
	qi::rule<Iterator, Source(), ascii::space_type> source;
};

template <typename Iterator>
void Grammar<Iterator>::initNames() {
	expr.name("expr");
	symbol.name("symbol");
	label.name("label");
	path.name("path");
	ref.name("ref");
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

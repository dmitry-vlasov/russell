#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "smm/sys.hpp"
#include "smm/adaptors.hpp"

namespace mdl { namespace smm { namespace parser {

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

inline void makeVars(Vect& expr) {
	for (auto& symb : expr)
		symb.var = true;
}

template<typename T>
inline void makeVars(vector<T*>& vars) {
	for (auto& v_it : vars)
		makeVars(v_it->expr);
}

inline void markVars(Vect& ex, const Vect& vars) {
	for (auto& s : ex) {
		if (contains(vars, s.lit))
			s.var = true;
	}
}

inline void markVars(const vector<Variables*>& vars, Vect& expr) {
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

struct Grammar : qi::grammar<LocationIter, smm::Source(), ascii::space_type> {

	struct AddToMath {
		template<typename T>
		struct result { typedef void type; };
		void operator()(Assertion* ass) const {
			makeVars(ass->variables);
			makeVars(ass->disjointed);
			markVars(ass->variables, ass->floating);
			markVars(ass->variables, ass->inner);
			markVars(ass->variables, ass->essential);
			markVars(ass->variables, ass->prop->expr);
			Sys::mod().math.assertions.add(ass->prop->label, ass);
		}
		void operator()(Constants* c) const {
			for (auto symb : c->expr)
				Sys::mod().math.constants.insert(symb);
		}
	};

	struct CreateLabel {
		template <typename T>
		struct result { typedef uint type; };
		uint operator()(const std::vector<char>& lab) const {
			string label(lab.begin(), lab.end());
			return Sys::mod().lex.labels.toInt(label);
		}
	};

	struct CreateSymb {
		template <typename T>
		struct result { typedef Symbol type; };
		Symbol operator()(const std::vector<char>& s) const {
			string symb(s.begin(), s.end());
			return Symbol(Sys::mod().lex.symbols.toInt(symb));
		}
	};

	struct ParseInclusion {
		template <typename T>
		struct result { typedef Inclusion* type; };
		Inclusion* operator()(string name) const {
			uint label = validate(name);
			Grammar::parse(label);
			return new Inclusion(label);
		}
	};

	struct SetLocation {
		template <typename T1, typename T2>
		struct result { typedef void type; };
		void operator()(Assertion* ass, LocationIter it) const {
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
		struct result { typedef Ref* type; };
		Ref* operator()(Ref::Type tp, uint ind, Assertion* ass) const {
			switch (tp) {
			case Ref::ESSENTIAL: return new Ref(ass->essential[ind]);
			case Ref::FLOATING:  return new Ref(ass->floating[ind]);
			case Ref::INNER:     return new Ref(ass->inner[ind]);
			case Ref::AXIOM:     return new Ref(ind, true);
			case Ref::THEOREM:   return new Ref(ind, false);
			default : assert(false && "impossible");
			}
			return new Ref(); // pacifying compiler
		}
	};

	Grammar();
	void initNames() {
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

	PropRefs prop_refs;
	HypRefs  hyp_refs;
	qi::rule<LocationIter, Vect(), ascii::space_type> expr;
	qi::rule<LocationIter, Symbol(), ascii::space_type> symbol;
	qi::rule<LocationIter, uint(),        ascii::space_type> label;
	qi::rule<LocationIter, std::string(), ascii::space_type> path;
	qi::rule<LocationIter, Ref(Assertion*), qi::locals<Ref::Type>, ascii::space_type> ref;
	qi::rule<LocationIter, Proof*(Assertion*), ascii::space_type> proof;
	qi::rule<LocationIter, Proposition(), ascii::space_type> provable;
	qi::rule<LocationIter, Proposition(), ascii::space_type> axiomatic;
	qi::rule<LocationIter, Essential*(), qi::locals<uint, Vect>, ascii::space_type> essential;
	qi::rule<LocationIter, Floating*(), qi::locals<uint, Vect>, ascii::space_type> floating;
	qi::rule<LocationIter, Inner*(), qi::locals<uint, Vect>, ascii::space_type> inner;
	qi::rule<LocationIter, Disjointed*(), ascii::space_type> disjointed;
	qi::rule<LocationIter, Variables*(), ascii::space_type> variables;
	qi::rule<LocationIter, Assertion*(), ascii::space_type> assertion;
	qi::rule<LocationIter, Constants*(), ascii::space_type> constants;
	qi::rule<LocationIter, Inclusion*(), ascii::space_type> inclusion;
	qi::rule<LocationIter, Comment*(), qi::unused_type> comment;
	qi::rule<LocationIter, Source(), ascii::space_type> source;

	static void parse(uint label) {
		if (Sys::mod().math.sources.has(label)) return;
		Source* src = new Source(label);
		src->read();
		Sys::mod().math.sources.add(label, src);
		LocationIter iter(src->data.begin(), src->name());
		LocationIter end(src->data.end(), src->name());
		if (!qi::phrase_parse(iter, end, Grammar(), qi::ascii::space, *src) || iter != end) {
			throw Error("parsing failed", src->name());
		}
	}
};

}}} // mdl::smm::parser

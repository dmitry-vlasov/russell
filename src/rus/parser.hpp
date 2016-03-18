#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "rus/globals.hpp"
#include "rus/adaptors.hpp"

namespace mdl { namespace rus {

namespace qi = boost::spirit::qi;
namespace ascii = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

inline Type* find_type(uint id, Location* loc = nullptr) {
	if (!Rus::get().math.types.has(id))
		throw Error("unknown type", show_id(id), loc);
	return Rus::get().math.types[id];
}

struct AddToMath {
	void operator()(Const* c) const {
		Rus::mod().math.consts.insert(c->symb);
	}
	void operator()(Type* t) const {
		Rus::mod().math.types[t->id] = t;
	}
	void operator()(Rule* r) const {
		r->type->rules.add(r->term, r);
		Rus::mod().math.rules[r->id] = r;
	}
};

struct SymbToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<char>& s) const {
		string symb(s.begin(), s.end());
		return Rus::mod().lex.symbs.toInt(symb);
	}
};

struct IdToInt {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<char>& id) const {
		string id_str(id.begin(), id.end());
		return Rus::mod().lex.ids.toInt(id_str);
	}
};

struct AddSymbol {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Expr& ex, Symbol s) const {
		return ex.push_back(s);
	}
};

struct ParseExpr {
	template <typename T1, typename T2, typename T3>
	struct result { typedef void type; };
	void operator()(Expr& ex, Type* tp, bool x) const {
		ex.type = tp;
		if (x) ex.parse();
	}
};


struct ParseImport {
	template <typename T>
	struct result { typedef Source* type; };
	Source* operator()(const string& path) const {
		// TODO
		return nullptr; //parse(path);
	}
};

struct FindType {
	template <typename T>
	struct result { typedef Type* type; };
	Type* operator()(uint id) const {
		return (id == (uint)-1) ? nullptr : find_type(id);
	}
};

struct AddDisjVar {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(vector<vector<Symbol>>& disj, Symbol v) const {
		disj.back().push_back(v);
	}
};

struct NewDisjSet {
	template <typename T>
	struct result { typedef void type; };
	void operator()(vector<vector<Symbol>>& disj) const {
		disj.push_back(vector<Symbol>());
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
struct Grammar : qi::grammar<Iterator, rus::Source(), ascii::space_type> {
	Grammar();
	void initNames();

	qi::rule<Iterator, Expr(Type*, bool), ascii::space_type> expr;
	qi::rule<Iterator, Symbol(), ascii::space_type> symb;
	qi::rule<Iterator, uint(),        ascii::space_type> id;
	qi::rule<Iterator, std::string(), ascii::space_type> path;
	qi::rule<Iterator, Disj(), ascii::space_type> disj;
	qi::rule<Iterator, Vars(), qi::locals<Symbol>, ascii::space_type> vars;
	qi::rule<Iterator, Hyp*(), qi::locals<uint>, ascii::space_type> hyp;
	qi::rule<Iterator, Prop*(), qi::locals<uint>, ascii::space_type> prop;
	qi::rule<Iterator, Proof*(), ascii::space_type> proof;
	qi::rule<Iterator, Theorem*(), ascii::space_type> theorem;
	qi::rule<Iterator, Def*(), ascii::space_type> def;
	qi::rule<Iterator, Axiom*(), qi::locals<Assertion&>, ascii::space_type> axiom;
	qi::rule<Iterator, Rule*(), ascii::space_type> rule;
	qi::rule<Iterator, Type*(), ascii::space_type> type;
	qi::rule<Iterator, Const*(), ascii::space_type> constant;
	qi::rule<Iterator, Source*(), ascii::space_type> import;
	qi::rule<Iterator, qi::unused_type, ascii::space_type> comment;
	qi::rule<Iterator, Source(), ascii::space_type> source;
};

template <typename Iterator>
void Grammar<Iterator>::initNames() {
	expr.name("expr");
	symb.name("symbol");
	id.name("id");
	path.name("path");
	disj.name("disjointed");
	vars.name("variables");
	prop.name("prop");
	hyp.name("hyp");
	proof.name("proof");
	theorem.name("theorem");
	def.name("def");
	axiom.name("axiom");
	rule.name("rule");
	type.name("type");
	constant.name("constant");
	comment.name("comment");
	import.name("import");
	source.name("source");
}

}} // mdl::rus

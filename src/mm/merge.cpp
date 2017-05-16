#define BOOST_SPIRIT_USE_PHOENIX_V3

#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "mm/sys.hpp"

namespace mdl { namespace mm { namespace {

struct Merged {
	static Merged& mod() { static Merged mrg; return mrg; }
	static const Merged& get() { return mod(); }
	stringstream contents;
};

void parse(const Path& path);

namespace qi      = boost::spirit::qi;
namespace ascii   = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

struct Add {
	template<typename T>
	struct result { typedef void type; };
	void operator()(const string& str) const {
		Merged::mod().contents << str;
	}
};

struct Include {
	template <typename T>
	struct result { typedef string type; };
	void operator()(const string& p) const {
		static set<string> included;
		if (included.count(p)) return;
		included.insert(p);
		Path path(p, Sys::conf().get("root"));
		parse(path);
	}
};

struct Grammar : qi::grammar<LocationIter, void(), ascii::space_type> {
	Grammar();
	void initNames();

	qi::rule<LocationIter, string(), qi::unused_type> contents;
	qi::rule<LocationIter, string(), qi::unused_type> inclusion;
	qi::rule<LocationIter, void(), ascii::space_type> source;
};

void Grammar::initNames() {
	inclusion.name("include");
	contents.name("contents");
	source.name("source");
}

Grammar::Grammar() : Grammar::base_type(source, "merge") {
	using qi::lit;
	using qi::lexeme;
	using namespace qi::labels;

	const phoenix::function<Add> add;
	const phoenix::function<Include> include;

	contents  %= lexeme[+(ascii::char_ - "$[")];
	inclusion %= lit("$[") > lexeme[+(ascii::char_ - "$]")] > "$]";
	source = + (inclusion [include(_1)] | contents  [add(_1)] );

	qi::on_error<qi::fail>(
		source,
		std::cout << phoenix::val("Syntax error. Expecting ") << _4
		<< phoenix::val(" here: \n") << _3 << phoenix::val("\n")
		<< phoenix::val("code: \n") << phoenix::construct<wrapper<>>(_3));
	initNames();
}


void remove_commented_imports(string& src) {
	stringstream ss;
	struct state {
		state() :
		in_comment(false), in_inclusion(), is_dollar(false) { }
		bool in_comment;
		bool in_inclusion;
		bool is_dollar;
	};
	state s;
	for (char ch : src) {
		bool prev_dollar = s.is_dollar;
		switch (ch) {
		case '$' : s.is_dollar = true; break;
		case '[' : if (prev_dollar) s.in_inclusion = true; break;
		case ']' : if (prev_dollar) s.in_inclusion = false; break;
		case '(' : if (prev_dollar) s.in_comment = true; break;
		case ')' : if (prev_dollar) s.in_comment = false; break;
		default: s.is_dollar = false;
		}
		if (!s.in_comment || !s.in_inclusion) ss << ch;
	}
	src = ss.str();
}

void parse(const Path& path) {
	string data;
	path.read(data);
	remove_commented_imports(data);
	LocationIter iter(data.begin(), Lex::toInt(path.name));
	LocationIter end(data.end(), Lex::toInt(path.name));
	bool r = phrase_parse(iter, end, Grammar(), ascii::space);
	if (!r || iter != end) {
		throw Error("parsing failed", path.name);
	}
}

}

void merge(uint src, uint tgt, uint tgt_sys) {
	Sys::timer()["merge"].start();
	Path in(Lex::toStr(src), Sys::conf().get("root"));
	parse(in);
	Path out(Lex::toStr(tgt), Sys::conf(tgt_sys).get("root"));
	ofstream os(out.path());
	os << Merged::get().contents.str();
	os.close();
	Sys::timer()["merge"].stop();
}


}} // mdl::mm::

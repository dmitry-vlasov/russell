
#define BOOST_SPIRIT_USE_PHOENIX_V3

#include "boost.hpp"
#include <mm_sys.hpp>

namespace mdl { namespace mm { namespace {

struct Merged {
	stringstream contents;
	set<string>  included;
};

void parse(const Path& path, Merged&);

namespace qi      = boost::spirit::qi;
namespace ascii   = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

struct AddContents {
	template<typename T>
	struct result { typedef void type; };
	void operator()(const string& str, Merged& merged) const {
		merged.contents << str;
	}
};

struct Include {
	template <typename T>
	struct result { typedef string type; };
	void operator()(const string& p, Merged& merged) const {
		if (merged.included.count(p)) return;
		merged.included.insert(p);
		Path path(p, Sys::conf().get("root"), "mm");
		parse(path, merged);
	}
};

struct Grammar : qi::grammar<LocationIter, void(), ascii::space_type> {
	Grammar(Merged& m) : Grammar::base_type(source, "merge"), merged(m)  {
		using qi::lit;
		using qi::lexeme;

		const phoenix::function<AddContents> add;
		const phoenix::function<Include> include;

		contents  %= lexeme[+(ascii::char_ - "$[")];
		inclusion %= lit("$[") > lexeme[+(ascii::char_ - "$]")] > "$]";
		source = + (inclusion [include(qi::labels::_1, phoenix::ref(merged))] | contents [add(qi::labels::_1, phoenix::ref(merged))] );

		qi::on_error<qi::fail>(
			source,
			std::cout << phoenix::val("Syntax error. Expecting ") << qi::labels::_4
			<< phoenix::val(" here: \n") << qi::labels::_3 << phoenix::val("\n")
			<< phoenix::val("code: \n") << phoenix::construct<wrapper<>>(qi::labels::_3));
		initNames();
	}
	void initNames() {
		inclusion.name("include");
		contents.name("contents");
		source.name("source");
	}

	Merged& merged;
	qi::rule<LocationIter, string(), qi::unused_type> contents;
	qi::rule<LocationIter, string(), qi::unused_type> inclusion;
	qi::rule<LocationIter, void(), ascii::space_type> source;
};

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

void parse(const Path& path, Merged& merged) {
	string data;
	path.read(data);
	remove_commented_imports(data);
	LocationIter iter(data.begin(), Lex::toInt(path.name()));
	LocationIter end(data.end(), Lex::toInt(path.name()));
	bool r = phrase_parse(iter, end, Grammar(merged), ascii::space);
	if (!r || iter != end) {
		throw Error("parsing failed", path.name());
	}
}

}

void merge(uint src, uint tgt, uint tgt_root) {
	Sys::timer()["merge"].start();
	Path in(Lex::toStr(src), Sys::conf().get("root"), "mm");
	Merged merged;
	parse(in, merged);
	Path out(Lex::toStr(tgt), Lex::toStr(tgt_root), "mm");
	ofstream os(out.path());
	os << merged.contents.str();
	os.close();
	Sys::timer()["merge"].stop();
}


}} // mdl::mm::

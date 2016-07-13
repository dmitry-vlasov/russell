#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "cut/ast.hpp"
#include "cut/globals.hpp"
#include "cut/adaptors.hpp"

namespace mdl { namespace cut {

namespace qi      = boost::spirit::qi;
namespace ascii   = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

struct Add {
	template<typename T>
	struct result { typedef void type; };
	void operator()(Section* s) const {
		cout << show(*s) << endl;
	}
	void operator()(string& str) const {
		cout << "\n<STR>\n" << str << "\n</STR>\n" << endl;
	}
};

struct MakeString {
	template <typename T>
	struct result { typedef string type; };
	string operator()(const vector<char>& s) const {
		return string(s.begin(), s.end());
	}
};


template <typename Iterator>
struct Grammar : qi::grammar<Iterator, void(), ascii::space_type> {
	Grammar();
	void initNames();

	qi::rule<Iterator, Type(), qi::unused_type> border;
	qi::rule<Iterator, string(), qi::unused_type> header;
	qi::rule<Iterator, Section*(), qi::unused_type> section;
	qi::rule<Iterator, string(), qi::unused_type> contents;
	qi::rule<Iterator, void(), ascii::space_type> source;
};

template <typename Iterator>
void Grammar<Iterator>::initNames() {
	border.name("border");
	header.name("header");
	section.name("section");
	contents.name("contents");
	source.name("source");
}

}} // mdl::cut

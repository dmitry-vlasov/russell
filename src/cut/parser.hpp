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
	void operator()(Paragraph* p) const {
	}
	void operator()(Chapter* ch) const {
	}
	void operator()(Part* p) const {
	}
	void operator()(string& str) const {
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

	qi::rule<Iterator, Paragraph*(), ascii::space_type> paragraph;
	qi::rule<Iterator, Chapter*(), ascii::space_type> chapter;
	qi::rule<Iterator, Part*(), ascii::space_type> part;
	qi::rule<Iterator, std::string(), ascii::space_type> contents;
	qi::rule<Iterator, void(), ascii::space_type> source;
};

template <typename Iterator>
void Grammar<Iterator>::initNames() {
	paragraph.name("paragraph");
	chapter.name("chapter");
	part.name("part");
	contents.name("contents");
	source.name("source");
}

}} // mdl::cut

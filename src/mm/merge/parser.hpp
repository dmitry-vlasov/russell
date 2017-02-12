#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "mm/merge/ast.hpp"

namespace mdl { namespace mm { namespace merge {

namespace qi      = boost::spirit::qi;
namespace ascii   = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

struct Add {
	template<typename T>
	struct result { typedef void type; };
	void operator()(const string& str, Merger* merger) const {
		merger->source << str;
	}
};

struct Include {
	template <typename T>
	struct result { typedef string type; };
	void operator()(const string& path, Merger* merger) const {
		static set<string> included;
		if (included.count(path)) return;
		included.insert(path);
		merger->read(Path(path));
	}
};

template <typename Iterator>
struct Grammar : qi::grammar<Iterator, void(), ascii::space_type> {
	Grammar(Merger* m);
	void initNames();

	qi::rule<Iterator, string(), qi::unused_type> contents;
	qi::rule<Iterator, string(), qi::unused_type> inclusion;
	qi::rule<Iterator, void(), ascii::space_type> source;

	Merger* merger;
};

template <typename Iterator>
void Grammar<Iterator>::initNames() {
	inclusion.name("include");
	contents.name("contents");
	source.name("source");
}

}}} // mdl::mm::merge

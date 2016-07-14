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

struct Stack {
	Section* source;
	Section* part;
	Section* chapter;
	Section* paragraph;
	Section* top;
};

static Stack stack;

struct Add {
	template<typename T>
	struct result { typedef void type; };
	void operator()(Section* sect) const {
		stack.top = sect;
		switch (sect->type) {
		case Type::PARAGRAPH:
			if (!stack.chapter) throw Error("empty chapter");
			stack.chapter->parts.push_back(sect);
			stack.paragraph = stack.chapter->parts.back();
			break;
		case Type::CHAPTER:
			if (!stack.part) throw Error("empty part");
			stack.part->parts.push_back(sect);
			stack.chapter = stack.part->parts.back();
			stack.paragraph = nullptr;
			break;
		case Type::PART:
			if (!stack.source) throw Error("empty source");
			stack.source->parts.push_back(sect);
			stack.part = stack.source->parts.back();
			stack.chapter = nullptr;
			stack.paragraph = nullptr;
			break;
		case Type::SOURCE:
			if (stack.source) throw Error("source already added");
			stack.source = sect;
			stack.part = nullptr;
			stack.chapter = nullptr;
			stack.paragraph = nullptr;
			break;
		default: throw Error("impossible");
		}
	}
	void operator()(string& str) const {
		stack.top->contents += str;
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
struct Grammar : qi::grammar<Iterator, Section*(), ascii::space_type> {
	Grammar();
	void initNames();

	qi::rule<Iterator, Type(), qi::unused_type> border;
	qi::rule<Iterator, string(), qi::unused_type> header;
	qi::rule<Iterator, Section*(), qi::unused_type> section;
	qi::rule<Iterator, string(), qi::unused_type> contents;
	qi::rule<Iterator, Section*(), ascii::space_type> source;
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

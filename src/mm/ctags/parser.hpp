#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include "mm/ast.hpp"
#include "mm/globals.hpp"
#include "mm/ctags/tags.hpp"

namespace mdl { namespace mm { namespace ctags {

namespace qi      = boost::spirit::qi;
namespace ascii   = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

struct CreateLabel {
	template <typename T>
	struct result { typedef uint type; };
	uint operator()(const std::vector<char>& lab) const {
		string label(lab.begin(), lab.end());
		for (char& ch : label) ch = (ch == '.') ? '_' : ch;
		return Mm::mod().lex.labels.toInt(label);
	}
};

struct AddTag {
	template <typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(unit label, Tag tag) const {

	}
};

struct LineIter : public string::const_iterator {
	LineIter(const string& f) :
	string::const_iterator(), file(f), beg(), end() { }
	LineIter(const LineIter& it) :
	string::const_iterator(it), file(it.file), beg(it.beg), end(it.end) { }
	LineIter(string::const_iterator it, const string& f) :
	string::const_iterator(it), file(f), beg(it.beg), end(it.end) { }

	void mark_begin() {
		beg = &string::const_iterator::operator*();
	}
	void mark_end() {
		end = &string::const_iterator::operator*();
	}
	string get_string() {
		if (beg && end) return string(beg, end);
		else return "";
	}
	/*
	LocationIter& operator ++() {
		char& curr = string::const_iterator::operator*();
		string::const_iterator::operator++();
		char& next = string::const_iterator::operator*();
		return *this;
	}
	LocationIter operator ++(int) {
		LocationIter curr(*this);
		inc(loc, *string::const_iterator::operator++());
		return curr;
	}*/
	string file;
	const char* beg;
	const char* end;
};


template<typename Iterator>
struct TrackLocation {
	TrackLocation(Iterator b) : beg(b), end(b) { }
    template <typename T1, typename T2>
    struct result { typedef void type; };
    void operator()(Tag& tag, Iterator it) const {
    	ass->loc = it.loc;
    }
    Iterator beg;
    Iterator end;
};


template <typename Iterator>
struct Grammar : qi::grammar<Iterator, Source(), ascii::space_type> {
	Grammar();
	void initNames();
	TrackLocation<Iterator> trackLocation;

	qi::rule<Iterator, void(), ascii::space_type> expr;
	qi::rule<Iterator, void(), ascii::space_type> symbol;
	qi::rule<Iterator, string(), ascii::space_type> label;
	qi::rule<Iterator, void(), ascii::space_type> path;
	qi::rule<Iterator, void(), ascii::space_type> ref;
	qi::rule<Iterator, void(), ascii::space_type> proof;
	qi::rule<Iterator, Tag(), qi::locals<string>, ascii::space_type> essential;
	qi::rule<Iterator, Tag(), qi::locals<string>, ascii::space_type> floating;
	qi::rule<Iterator, void(), ascii::space_type> disjointed;
	qi::rule<Iterator, void(), ascii::space_type> variables;
	qi::rule<Iterator, Tag(), qi::locals<string>, ascii::space_type> axiom;
	qi::rule<Iterator, Tag(), qi::locals<string>, ascii::space_type> theorem;
	qi::rule<Iterator, void(), ascii::space_type> constants;
	qi::rule<Iterator, void(Source&), ascii::space_type> node;
	qi::rule<Iterator, void(), ascii::space_type> block;
	qi::rule<Iterator, void(), ascii::space_type> inclusion;
	qi::rule<Iterator, void(), qi::unused_type> comment;
	qi::rule<Iterator, Source(), ascii::space_type> source;
};

template <typename Iterator>
void Grammar<Iterator>::initNames() {
	symbol.name("symbol");
	label.name("label");
	path.name("path");
	expr.name("expr");
	ref.name("ref");
	proof.name("proof");
	theorem.name("theorem");
	axiom.name("axiom");
	essential.name("essential");
	floating.name("floating");
	disjointed.name("disjointed");
	variables.name("variables");
	node.name("node");
	block.name("block");
	constants.name("constants");
	comment.name("name");
	inclusion.name("inclusion");
	source.name("source");
}

}}} // mdl::mm::parser

#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_object.hpp>

#include <boost/algorithm/string.hpp>

#include "mm/cut/ast.hpp"
#include "mm/cut/adaptors.hpp"

namespace mdl { namespace mm { namespace cut {

namespace qi      = boost::spirit::qi;
namespace ascii   = boost::spirit::ascii;
namespace phoenix = boost::phoenix;

namespace {

	string init_dir (Section* sect) {
		string dir;
		const Section* par = sect->parent;
		while (par && par->file.size()) {
			if (par->parent)
				dir = par->file + "/" + dir;
			else
				dir = par->dir + par->file + "/" + dir;
			par = par->parent;
		}
		return dir;
	}

	void init_paths(Section* sect) {
		static set<string> names;
		string dir = init_dir(sect);
		bool has_endline = (*sect->name.rbegin() == '\n');

		string orig_name = sect->name;
		boost::trim_right(orig_name);
		for (int i = 0; names.count(dir + sect->name); ++i) {
			sect->name = orig_name + "_" + to_string(i);
			//cout << "making new name: " << sect->name << endl;
		}
		names.insert(dir + sect->name);
		if (has_endline) sect->name += '\n';

		if (!sect->file.size()) {
			sect->file = sect->name;
			boost::trim(sect->file);
			boost::replace_all(sect->file, " ", "_");
			boost::replace_all(sect->file, "/", "_");
			boost::replace_all(sect->file, ":", "_");
			boost::replace_all(sect->file, ".", "_");
			boost::replace_all(sect->file, "?", "_");
			boost::replace_all(sect->file, "!", "_");
			boost::replace_all(sect->file, "$", "_");
			boost::replace_all(sect->file, "\\", "_");
			boost::replace_all(sect->file, "'", "_");
			sect->dir = dir;
			sect->path = sect->dir + sect->file + ".mm";
		}
	}
}

struct Stack {
	Stack() :
	source(nullptr), part(nullptr), chapter(nullptr),
	paragraph(nullptr), last(nullptr) { }
	Section* source;
	Section* part;
	Section* chapter;
	Section* paragraph;
	Section* last;
};

static Stack stack;

struct Add {
	template<typename T1, typename T2>
	struct result { typedef void type; };
	void operator()(Section* sect, string root) const {
		sect->root = root;
		sect->prev_sect = stack.last;
		if (stack.last)
			stack.last->next_sect = sect;
		stack.last = sect;
		switch (sect->type) {
		case Type::PARAGRAPH:
			//cout << "paragraph: " << sect->name << endl;
			if (!stack.chapter) throw Error("empty chapter");
			sect->parent = stack.chapter;
			stack.chapter->parts.push_back(sect);
			sect->prev_sibling = stack.paragraph;
			if (stack.paragraph)
				stack.paragraph->next_sibling = sect;
			stack.paragraph = stack.chapter->parts.back();
			break;
		case Type::CHAPTER:
			//cout << "chapter: " << sect->name << endl;
			if (!stack.part) throw Error("empty part");
			sect->parent = stack.part;
			stack.part->parts.push_back(sect);
			sect->prev_sibling = stack.chapter;
			if (stack.chapter)
				stack.chapter->next_sibling = sect;
			stack.chapter = stack.part->parts.back();
			stack.paragraph = nullptr;
			break;
		case Type::PART:
			//cout << "part: " << sect->name << endl;
			if (!stack.source) throw Error("empty source");
			sect->parent = stack.source;
			stack.source->parts.push_back(sect);
			sect->prev_sibling = stack.part;
			if (stack.part)
				stack.part->next_sibling = sect;
			stack.part = stack.source->parts.back();
			stack.chapter = nullptr;
			stack.paragraph = nullptr;
			break;
		case Type::SOURCE:
			//cout << "source: " << sect->name << endl;
			if (stack.source) throw Error("source already added");
			sect->parent = nullptr;
			stack.source = sect;
			stack.part = nullptr;
			stack.chapter = nullptr;
			stack.paragraph = nullptr;
			break;
		default: throw Error("impossible");
		}
		init_paths(sect);
	}
	void operator()(string& str) const {
		stack.last->contents += str;
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
struct Grammar : qi::grammar<Iterator, Section*(), qi::unused_type> {
	Grammar(string root);
	void initNames();

	string root;

	qi::rule<Iterator, Type(), qi::unused_type> border;
	qi::rule<Iterator, string(), qi::unused_type> header;
	qi::rule<Iterator, Section*(), qi::unused_type> section;
	qi::rule<Iterator, string(), qi::unused_type> contents;
	qi::rule<Iterator, Section*(), qi::unused_type> source;
};

template <typename Iterator>
void Grammar<Iterator>::initNames() {
	border.name("border");
	header.name("header");
	section.name("section");
	contents.name("contents");
	source.name("source");
}

}}} // mdl::mm::cut

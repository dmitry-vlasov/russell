#pragma once

namespace mdl { namespace mm { namespace ctags {

class Tag {
	enum Kinds {
		FLOATING,
		ESSENTIAL,
		AXIOMATIC,
		PROVABLE
	};
	struct Kind {
		char   letter;        // kind letter
		string name;		  // kind name
		string description;	  // displayed in --help output
	};
	static Kind kinds[] = {
	  { 'f', "floating",    "floating hypothesis $f" },
	  { 'e', "essential",   "essential hypothesis $e" },
	  { 'a', "axiomatic",   "axiomatic assertion $a" },
	  { 'p', "provable",    "provable assertion $p" }
	};

	Tag(Kind k, const string& l) : kind (k), label(l) { }
	Kinds  kind;
	string label;
	string text;
	bool operator < (const Tag& tag) const {
		return label < tag.label;
	}
	void write(ofstream& s) const {
		s << label << '\t'
	}
};

struct Source {
	Source(const string& r, const string& n) : root(r), name(n), tags() {
		boost::erase_last(name, ".smm");
		boost::erase_last(name, ".mm");
	}
	string root;
	string name;
	string path() { return (root.size() ? root + "/" + name : name) + ".mm"; }
	string dir() { string p = path(); return p.substr(0, p.find_last_of("/")) + "/"; }
	set<Tag> tags;
};


}}}

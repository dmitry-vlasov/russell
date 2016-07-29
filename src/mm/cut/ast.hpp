#pragma once

#include "common.hpp"

namespace mdl { namespace mm { namespace cut {

#define PARAGRAPH_STR "=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-="
#define CHAPTER_STR   "#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#"
#define PART_STR      "###############################################################################"

#define FULL_PARAGRAPH_STR "$(\n=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-="
#define FULL_CHAPTER_STR   "$(\n#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#"
#define FULL_PART_STR      "$(\n###############################################################################"

enum class Type { PARAGRAPH, CHAPTER, PART, SOURCE };

inline string border(const Type tp) {
	switch (tp) {
	case Type::PARAGRAPH : return PARAGRAPH_STR;
	case Type::CHAPTER   : return CHAPTER_STR;
	case Type::PART      : return PART_STR;
	case Type::SOURCE    : return "";
	default        : return "<none>";
	}
}

struct Section {
	Section() : type(Type::SOURCE), header(), name(), footer(),
	contents(), dir(), file(), path(),
	prev_sect(nullptr), next_sect(nullptr),
	prev_sibling(nullptr), next_sibling(nullptr),
	parent(nullptr), parts() { }
	~ Section() { for (auto* p : parts) delete p; }
	void save() const;
	Type   type;
	string header;
	string name;
	string footer;
	string contents;
	string dir;
	string file;
	string path;
	Section* prev_sect;
	Section* next_sect;
	Section* prev_sibling;
	Section* next_sibling;
	Section* parent;
	vector<Section*> parts;
};

string show_all(const Section&);
string show_contents(const Section&);
inline ostream& operator << (ostream& os, const Section& sect) {
	os << show_all(sect);
	return os;
}

Section* parse(const string& root, string in, const string& out);
void split(Section* src);
void save(Section* src);

}}} // mdl::mm::cut



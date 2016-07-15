#pragma once

#include "common.hpp"

namespace mdl { namespace cut {

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
	~ Section() { for (auto* p : parts) delete p; }
	void save() const;
	Type   type;
	string header;
	string name;
	string footer;
	string contents;
	string dir;
	string file;
	const Section* parent;
	vector<Section*> parts;
};

string show_all(const Section&);
string show_contents(const Section&);
inline ostream& operator << (ostream& os, const Section& sect) {
	os << show_all(sect);
	return os;
}

}} // mdl::cut



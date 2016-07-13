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

inline string section_str(const Type tp) {
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
	Type   type;
	string header;
	string name;
	string footer;
	string contents;
	string file;
	vector<Section*> parts;
};

string show(const Section&);

}} // mdl::cut



#pragma once

#include "common.hpp"

namespace mdl { namespace cut {

#define PARAGRAPH_STR "=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-="
#define CHAPTER_STR   "#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#"
#define PART_STR      "###############################################################################"

#define FULL_PARAGRAPH_STR "$(\n=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-="
#define FULL_CHAPTER_STR   "$(\n#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#"
#define FULL_PART_STR      "$(\n###############################################################################"

enum class Type { PARAGRAPH, CHAPTER, PART };

inline string section_str(const Type tp) {
	switch (tp) {
	case Type::PARAGRAPH : return PARAGRAPH_STR;
	case Type::CHAPTER   : return CHAPTER_STR;
	case Type::PART      : return PART_STR;
	default        : return "<none>";
	}
}

struct Section {
	Type   type;
	string header;
	string name;
	string footer;
};

struct Paragraph {
	string file;
	string name;
	string descr;
	string contents;
};

struct Chapter {
	~ Chapter();
	string file;
	string name;
	string descr;
	string contents;
	vector<Paragraph*> paragraphs;
};

struct Part {
	~ Part();
	string file;
	string name;
	string descr;
	string contents;
	vector<Chapter*> chapters;
};

struct Source {
	Source(const string& n) :
	file(n), name(), descr(), contents(), parts() { }
	~ Source();
	string file;
	string name;
	string descr;
	string contents;
	vector<Part*> parts;
};

inline Chapter::~Chapter() { for (auto* p : paragraphs) delete p; }
inline Part::~Part() { for (auto* ch : chapters) delete ch; }
inline Source::~Source() { for (auto* p : parts) delete p; }

string show(const Section&);
string show(const Paragraph&);
string show(const Chapter&);
string show(const Part&);
string show(const Source&);

}} // mdl::cut



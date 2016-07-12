#pragma once

#include "common.hpp"

namespace mdl { namespace cut {

#define PARAGRAPH "=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-="
#define CHAPTER   "#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#"
#define PART      "###############################################################################"

#define FULL_PARAGRAPH "$(\n=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-="
#define FULL_CHAPTER   "$(\n#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#"
#define FULL_PART      "$(\n###############################################################################"

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

string show(const Paragraph&);
string show(const Chapter&);
string show(const Part&);
string show(const Source&);

}} // mdl::cut



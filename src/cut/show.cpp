#include "cut/ast.hpp"

namespace mdl { namespace cut {



string show(const Section& s) {
	string str;
	str += "\n<SECTION>\n";
	str += "$(\n";
	str += s.header;
	str += section_str(s.type);
	str += s.name;
	str += section_str(s.type);
	str += s.footer;
	str += "$)\n";
	return str;
}

/*
string show(const Paragraph& p) {
	string str;
	str += "\n<PARAGPRAPH>\n";
	str += "$(\n";
	str += string(PARAGRAPH_STR) + "\n";
	str += p.name;
	str += string(PARAGRAPH_STR) + "\n";
	str += p.descr;
	str += "$)\n";
	str += p.contents;
	return str;
}

string show(const Chapter& ch) {
	string str;
	str += "\n<CHAPTER>\n";
	str += "$(\n";
	str += string(CHAPTER_STR) + "\n";
	str += ch.name;
	str += string(CHAPTER_STR) + "\n";
	str += ch.descr;
	str += "$)\n";
	str += ch.contents;
	return str;
}


string show(const Part& p) {
	string str;
	str += "\n<PART>\n";
	str += "$(\n";
	str += string(PART_STR) + "\n";
	str += p.name;
	str += string(PART_STR) + "\n";
	str += p.descr;
	str += "$)\n";
	str += p.contents;
	return str;
}

string show(const Source& s) {
	string str;
	str += s.name + "\n";
	str += s.descr + "\n";
	str += s.contents;
	return str;
}
*/

}} // mdl::cut

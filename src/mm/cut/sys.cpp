#include <boost/filesystem.hpp>
#include <boost/algorithm/string.hpp>

#include "mm/cut/ast.hpp"
#include "mm/cut/patches.cpp"
#include "mm/cut/grammar.hpp"

namespace mdl { namespace mm { namespace cut {

string show_contents(const Section& s);

namespace fs = boost::filesystem;

void Section::save() const {
	if (dir.size() && !fs::exists(dir))
		fs::create_directories(dir);
	ofstream out(path);
	out << show_contents(*this) << endl;
	for (Section* s : parts) {
		out << "$[ " << s->path << " $]\n";
	}
	out.close();
}

namespace {

void split_section(Section* sect) {
	if (sect->type == Type::PARAGRAPH) return;
	string cont = sect->contents;
	boost::trim(cont);
	if (!cont.size()) return;

	Section* header = new Section;
	header->name = sect->name;
	header->footer = sect->footer;
	header->contents = sect->contents;
	header->file = sect->file;
	header->dir = sect->dir + sect->file + "/";
	header->path = header->dir + header->file + ".mm";
	switch (sect->type) {
	case Type::PARAGRAPH: assert(false && "impossible"); break;
	case Type::CHAPTER:   header->type = Type::PARAGRAPH; break;
	case Type::PART:      header->type = Type::CHAPTER;   break;
	case Type::SOURCE:    header->type = Type::PART;      break;
	}
	sect->contents.clear();

	header->prev_sect = sect->prev_sect;
	header->next_sect = sect;
	header->prev_sect->next_sect = header;
	header->next_sect->prev_sect = header;

	header->prev_sibling = nullptr;
	header->next_sibling = header->next_sect;
	header->next_sibling->prev_sibling = header;
	sect->incs.push_back(header);
}

} // anonymous namespace

void Cutter::read(Path in) {
	string data;
	in.read(data);
	patch(data);

	LocationIter iter(data.begin(), in.name);
	LocationIter end(data.end(), in.name);

	size_t slash_pos = in.name.find_last_of("/");
	size_t dot_pos = in.name.find_last_of(".");
	size_t len = in.name.size();
	if (slash_pos != string::npos) len -= slash_pos;
	if (dot_pos != string::npos)   len -= len - dot_pos;

	Section* sect = new Section;
	sect->file = in.name.substr(slash_pos == string::npos ? 0 : slash_pos, len);
	sect->dir  = in.root;
	sect->path = source->dir + "/" + sect->file + ".mm";
	sect->type = Type::SOURCE;

	bool r = phrase_parse(iter, end, Grammar<LocationIter>(), ascii::space, source);
	if (!r || iter != end) {
		throw Error("parsing failed", in.name);
	}
	source.reset(sect);
}


void Cutter::split() {
	Section* s = source.get();
	while (s) {
		split_section(s);
		s = s->next_sect;
	}
}

void Cutter::save(Path out) {
	Section* sect = source.get();
	sect->dir = out.root;
	while (sect) {
		sect->save();
		sect = sect->next_sect;
	}
}

}}} // mdl::mm::cut

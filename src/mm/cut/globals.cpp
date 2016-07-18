#include <boost/filesystem.hpp>
#include <boost/algorithm/string.hpp>

#include "mm/cut/ast.hpp"
#include "mm/cut/globals.hpp"

namespace mdl { namespace mm { namespace cut {

namespace fs = boost::filesystem;

void Cut::run() {
	timer.start();
	if (config.verbose)
		cout << "cutting file " << config.in << " ... " << flush;
	if (!parse()) return;
	if (!save())  return;
	timer.stop();
	if (config.verbose)
		cout << "done in " << timer << endl;
}

bool Cut::parse() {
	try {
		cut::parse(config.in);
		return true;
	} catch (Error& err) {
		error += '\n';
		error += err.what();
		return false;
	}
}

namespace {

void split_section(Section* sect) {
	if (sect->type == Type::PARAGRAPH) return;
	string cont = sect->contents;
	boost::trim(cont);
	if (!cont.size()) return;

	Section* header = new Section;
	header->name = sect->name;
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

	//cout << "Splitting: " << show_contents(*header) << endl;
	//cout << "Splitting: " << endl << header->path << endl;

	header->prev_sect = sect->prev_sect;
	header->next_sect = sect;
	header->prev_sect->next_sect = header;
	header->next_sect->prev_sect = header;

	header->prev_sibling = nullptr;
	header->next_sibling = header->next_sect;
	header->next_sibling->prev_sibling = header;
}

void split_sections(Section* src) {
	Section* s = src;
	while (s) {
		split_section(s);
		s = s->next_sect;
	}
}

}

bool Cut::save() {
	try {
		if (!config.out.size()) return false;
		if (config.out.substr(config.out.size() - 3) != ".mm") return false;
		split_sections(source);
		Section* sect = source;
		while (sect) {
			sect->save();
			sect = sect->next_sect;
		}
		return true;
	} catch (Error& err) {
		error += '\n';
		error += err.what();
		return false;
	}
}

void Section::save() const {
	if (type != Type::SOURCE)
		fs::create_directories(dir);

	//cout << endl << "writing: " << path << endl;

	ofstream out(path);
	out << show_contents(*this) << endl;
	for (Section* s : parts) {
		out << "$[ " << s->path << " $]\n";
	}
	out.close();
}

}}} // mdl::mm::cut

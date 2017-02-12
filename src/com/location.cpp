#include <boost/algorithm/string.hpp>
#include "common.hpp"
#include "location.hpp"

namespace mdl {

inline void inc(Location&loc, char ch) {
	++ loc.pos;
	if (ch == '\n') {
		loc.col = 0;
		++ loc.line;
	} else
		++ loc.col;
}

LocationIter& LocationIter::operator ++() {
	inc(loc, *string::const_iterator::operator++());
	return *this;
}

LocationIter LocationIter::operator ++(int) {
	LocationIter curr(*this);
	inc(loc, *string::const_iterator::operator++());
	return curr;
}

inline string cut_outer_directory(string path) {
	size_t slash_pos = path.find_first_of("/");
	return path.substr(slash_pos == string::npos ? 0 : slash_pos + 1);
}

Path Path::open() {
	Path p(*this);
	ifstream in;
	while (true) {
		in.open(p.path(), std::ios_base::in);
		if (!in.fail()) break;
		string shorter = cut_outer_directory(p.name);
		if (p.name == shorter) {
			throw Error("Could not open input file", path());
		} else
			p.name = shorter;
	}
	in.close();
	return p;
}

void Path::read(string& data) {
	ifstream in(path());
	in.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(in),
		std::istream_iterator<char>(),
		std::back_inserter(data));
	in.close();
}

void Path::write(const string& data) {
	ofstream out(path());
	std::copy(
		data.begin(),
		data.end(),
		std::ostream_iterator<char>(out));
	out.close();
}

}

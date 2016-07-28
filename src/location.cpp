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

ifstream open_smart(string path, string root) {
	boost::trim(path);
	boost::trim(root);
	if (root.size() && root.back() != '/')
		root += '/';
	ifstream is;
	while (true) {
		string full_path = root + path;
		is.open(full_path, std::ios_base::in);
		if (is.is_open())
			return is;
		string shorter = cut_outer_directory(path);
		if (path == shorter)
			throw Error("Could not open input file");
		else
			path = shorter;
	}
}

}

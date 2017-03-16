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

void Path::read(string& data) const {
	ifstream in(path());
	in.unsetf(std::ios::skipws);
	std::copy(
		std::istream_iterator<char>(in),
		std::istream_iterator<char>(),
		std::back_inserter(data));
	in.close();
}

void Path::write(const string& data) const {
	ofstream out(path());
	std::copy(
		data.begin(),
		data.end(),
		std::ostream_iterator<char>(out));
	out.close();
}

}

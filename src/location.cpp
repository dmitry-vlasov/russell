#include "location.hpp"

namespace mdl {

inline void inc(Location&loc, char ch) {
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

}

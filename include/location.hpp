#pragma once

#include "std.hpp"

namespace mdl { 

struct Location {
	Location() :
	line(0), col(0), pos(0), file() { }
	Location(const string& f) :
	line(0), col(0), pos(0), file(f) { }
	Location(const Location& loc) :
	line(loc.line), col(loc.col), pos(loc.pos), file(loc.file) { }

	Location& operator = (const Location& loc) {
		line = loc.line;
		col  = loc.col;
		pos  = loc.pos;
		if (file.empty())
			file = loc.file;
		return *this;
	}

	uint   line;
	uint   col;
	uint   pos;
	string file;
};

struct LocationIter : public string::const_iterator {
	LocationIter(const LocationIter& it) :
	string::const_iterator(it), loc(it.loc) { }
	LocationIter(string::const_iterator it, const string& file) :
	string::const_iterator(it), loc(file) { }

	LocationIter& operator ++();
	LocationIter operator ++(int);
	Location loc;
};

inline ostream& operator << (ostream& os, const Location& loc) {
	os << "file: " << loc.file << " ";
	os << "line: " << to_string(loc.line + 1) << " ";
	os << "col: " << to_string(loc.col + 1);
	return os;
}
inline string show(const Location& loc) {
	ostringstream os;
	os << loc;
	return os.str();
}

inline ostream& operator << (ostream& os, const LocationIter& it){
	os << show(it.loc);
	return os;
}

} 

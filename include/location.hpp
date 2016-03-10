#pragma once

#include "std.hpp"

namespace mdl { 

struct Location {
	Location() :
	line(0), col(0), file() { }
	Location(const string& f) :
	line(0), col(0), file(f) { }
	Location(const Location& loc) :
	line(loc.line), col(loc.col), file(loc.file) { }

	Location& operator = (const Location& loc) {
		line = loc.line;
		col  = loc.col;
		if (file.empty())
			file = loc.file;
		return *this;
	}

	uint   line;
	uint   col;
	string file;
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

} 

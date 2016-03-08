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

	void show (string& str) const {
		str += "file: ";
		str += file;
		str += " line: ";
		str += std::to_string(line + 1);
		str += " col: ";
		str += std::to_string(col + 1);
	}

	uint   line;
	uint   col;
	string file;
};

} 

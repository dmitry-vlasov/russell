#pragma once

#include "std.hpp"
#include "lex.hpp"

namespace mdl { 

struct Indent {
	int  num;
	char del;

	Indent(int n = 1, char d = '\t') : num(n), del(d) {
	}
	void write(ostream& os) const {
		int n = num;
		while (n --) os << del;
	}
	static string paragraph(const string& str, string d = "\t") {
		string indented;
		for (char ch : str) {
			if (ch == '\n') indented += "\n" + d;
			else            indented += ch;
		}
		return indented;
	}
	string str() const {
		string s;
		int n = num;
		while (n--) s += del;
		return s;
	}
};


inline ostream& operator << (ostream& os, Indent ind) {
	ind.write(os);
	return os;
}

template<int len_f = 64, int len_b = 8>
struct wrapper {
	wrapper(string::const_iterator it) :
	str (it - len_b, it + len_f){ }
	string str;
};

template<int len_f, int len_b>
ostream& operator << (ostream& os, const wrapper<len_f, len_b>& wr){
	os << wr.str;
	return os;
}

struct Location {
	Location() :
	line(0), col(0), pos(0), file(-1) { }
	Location(uint f) :
	line(0), col(0), pos(0), file(f) { }
	Location(const Location& loc) :
	line(loc.line), col(loc.col), pos(loc.pos), file(loc.file) { }

	Location& operator = (const Location& loc) {
		line = loc.line;
		col  = loc.col;
		pos  = loc.pos;
		file = loc.file;
		return *this;
	}

	uint line;
	uint col;
	uint pos;
	uint file;

	string show() const {
		string s;
		s += "file: " + Lex::toStr(file) + " ";
		s += "line: " + to_string(line + 1) + " ";
		s += "col: "  + to_string(col + 1);
		return s;
	}
};

struct LocationIter : public string::const_iterator {
	LocationIter(const LocationIter& it) :
	string::const_iterator(it), loc(it.loc) { }
	LocationIter(string::const_iterator it, uint file) :
	string::const_iterator(it), loc(file) { }

	LocationIter& operator ++() {
		inc(loc, *string::const_iterator::operator++());
		return *this;
	}
	LocationIter operator ++(int) {
		LocationIter curr(*this);
		inc(loc, *string::const_iterator::operator++());
		return curr;
	}
	Location loc;

private :
	void inc(Location&loc, char ch) {
		++ loc.pos;
		if (ch == '\n') { loc.col = 0; ++ loc.line; }
		else ++ loc.col;
	}
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

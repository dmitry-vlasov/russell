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
		if (!str.size()) return "";
		string indented(d);
		for (auto i = str.begin(); i != str.end(); ++ i) {
			if (*i == '\n' && i + 1 != str.end()) indented += "\n" + d;
			else indented += *i;
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
	Location(uint f, const string& e = "", const string& r = "") :
	line(0), col(0), pos(0), file(f), ext(e), root(r) { }
	Location(const Location& loc) :
	line(loc.line), col(loc.col), pos(loc.pos), file(loc.file), ext(loc.ext), root(loc.root) { }

	Location& operator = (const Location& loc) {
		line = loc.line;
		col  = loc.col;
		pos  = loc.pos;
		file = loc.file;
		ext  = loc.ext;
		root = loc.root;
		return *this;
	}

	uint line;
	uint col;
	uint pos;
	uint file;
	string ext;
	string root;

	string show() const {
		string s;
		s += "path: " + root + "/" + Lex::toStr(file) + "." + ext + "\n";
		s += "line: " + to_string(line + 1) + "\n";
		s += "col: "  + to_string(col + 1) + "\n";
		return s;
	}
	string xml() const {
		string s;
		s += "path=\"" + root + "/" + Lex::toStr(file) + "." + ext + "\" ";
		s += "line=\"" + to_string(line + 1) + "\" ";
		s += "col=\""  + to_string(col + 1) + "\" ";
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

template<class S>
struct Token {
	typedef S Source;

	Token() : src(nullptr), beg(nullptr), end(nullptr) { }
	Token(Source* s) : src(s), beg(nullptr), end(nullptr) { }
	Token(Source* s, const char* b, const char* e) :
	src(s), beg(b), end(e) { }
	Source*     src;
	const char* beg;
	const char* end;

	bool preceeds (const Token<S>& t) {
		if (t.src->includes.count(src)) return true;
		if (t.src == src) return end <= t.beg;
		return false;
	}

	string show() const {
		LocationIter b (src->data.begin(), src->id());
		LocationIter e (string::const_iterator(beg), src->id());
		LocationIter x = b;
		while (x != e) ++x;
		return x.loc.show();
	}
	Location locate() const {
		Location loc(
			src->id(),
			Source::Sys::ext(),
			Source::Sys::conf(src->sys()).get("root")
		);
		const char* mid = beg + length() / 2;
		const char* s = src->data.c_str();
		while (s) {
			if (*s++ == '\n') { ++loc.line; loc.col = 0; } else ++loc.col;
			if (s == mid) return loc;
		}
		return Location();
	}

	bool is_defined() const { return src && beg && end; }
	operator bool() const { return is_defined(); }
	string str() const { return string(beg, end); }
	uint length() const { return beg <= end ? end - beg : 0; }
};

template<class S>
inline bool operator < (const Token<S>& l, const Token<S>& r) {
	return l.end <= r.beg;
}

template<class S>
struct Tokenable {
	Tokenable(const Token<S>& t) : token(t) { }
	Tokenable(const Tokenable& t) : token(t.token) { }
	virtual ~Tokenable() { }
	void operator = (const Tokenable& t) { token = t.token; }
	Token<S> token;
};

template<class S>
struct Id : public Tokenable<S> {
	Id(uint i = -1, const Token<S>& t = Token<S>()) : Tokenable<S>(t), id(i) { }
	uint id;
	string toStr() const { return Lex::toStr(id); }
};

template<class S>
struct TokenIter : public string::const_iterator {
	typedef S Source;
	TokenIter(const TokenIter& it) :
	string::const_iterator(it) { }
	TokenIter(string::const_iterator it, Source* src) :
	string::const_iterator(it), token_(src) { }

	TokenIter& operator ++() {
		inc(loc, *string::const_iterator::operator++());
		return *this;
	}
	TokenIter operator ++(int) {
		TokenIter curr(*this);
		inc(loc, *string::const_iterator::operator++());
		return curr;
	}

	void start() {
		token.beg = &string::const_iterator::operator*();
	}
	void end() {
		token.end = &string::const_iterator::operator*();
	}
	Token<Source> token() const {
		return token_;
	}

private :
	Token<Source> token_;
	Location loc;

	void inc(Location&loc, char ch) {
		++ loc.pos;
		if (ch == '\n') { loc.col = 0; ++ loc.line; }
		else ++ loc.col;
	}
};

inline const char* locate_position(const uint line, const uint col, const char* src) {
	uint l = 0, c = 0;
	while (src) {
		if (*src++ == '\n') { ++l; c = 0; } else ++c;
		if (l == line && c == col) return src;
	}
	return nullptr;
}

inline ostream& operator << (ostream& os, const Location& loc) {
	os << "file: " << Lex::toStr(loc.file) << " ";
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

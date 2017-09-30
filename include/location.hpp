#pragma once

#include "std.hpp"
#include "lex.hpp"
#include "xml.hpp"

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
		s += "path=\"" + root + "/" + escape_xml(Lex::toStr(file)) + "." + ext + "\" ";
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

enum class TokenType { FULL, SEMI, NONE, DEFAULT = FULL };
template<class S, TokenType T = TokenType::DEFAULT> class TokenStorage;

template<class S>
struct TokenStorage<S, TokenType::FULL> {
	typedef S Source;
	TokenStorage() : src_(nullptr), beg_(nullptr), end_(nullptr) { }
	TokenStorage(Source* s) : src_(s), beg_(nullptr), end_(nullptr) { }
	TokenStorage(Source* s, const char* b, const char* e) :
	src_(s), beg_(b), end_(e) { }

	Source* src() { return src_; }
	const Source* src() const { return src_; }
	const char* beg() const { return beg_; }
	const char* end() const { return end_; }
	void set(Source* s, const char* b, const char* e) {
		src_ = s; beg_ = b; end_ = e;
	}

private:
	Source*     src_;
	const char* beg_;
	const char* end_;
};

template<class S>
struct TokenStorage<S, TokenType::NONE> {
	typedef S Source;
	TokenStorage() { }
	TokenStorage(Source* s) { }
	TokenStorage(Source* s, const char* b, const char* e) { }

	Source* src() { return nullptr; }
	const Source* src() const { return nullptr; }
	const char* beg() const { return nullptr; }
	const char* end() const { return nullptr; }
	void set(Source* s, const char* b, const char* e) { }
};

template<class S>
struct TokenStorage<S, TokenType::SEMI> {
	typedef S Source;
	TokenStorage() {
		sys_ = UNDEF_SRC;
		src_ = UNDEF_SRC;
		beg_ = UNDEF_PTR;
		end_ = UNDEF_PTR;
	}
	TokenStorage(Source* s) {
		set_src(s);
		beg_ = UNDEF_PTR;
		end_ = UNDEF_PTR;
	}
	TokenStorage(Source* s, const char* b, const char* e) : TokenStorage(s) {
		set(s, b, e);
	}

	Source* src() {
		return
			src_ == UNDEF_SRC ?
			nullptr :
			Source::Sys::mod(sys_).math.template get<Source>().access(get_src());
	}
	const Source* src() const {
		return
			src_ == UNDEF_SRC ?
			nullptr :
			Source::Sys::get(sys_).math.template get<Source>().access(get_src());
	}
	const char* beg() const {
		return
			src() ?
			(beg_ == UNDEF_PTR ? nullptr : src()->data.c_str() + beg_) :
			nullptr;
	}
	const char* end() const {
		return
			src() ?
			(end_ == UNDEF_PTR ? nullptr : src()->data.c_str() + end_) :
			nullptr;
	}
	void set(Source* s, const char* b, const char* e) {
		set_src(s);
		beg_ = b - s->data.c_str();
		end_ = e - s->data.c_str();
		if (!(s == src() && b == beg() && e == end())) {
			cerr << "DON'T MATCH: " << endl;
			exit(1);
		}
		cout << string(beg(), end_ - beg_) << endl;
	}

private:
	enum {
		//UNDEF_SRC = 0xFFFF,
		//UNDEF_PTR = 0xFFFFFF
		UNDEF_SRC = -1, //0xFFFFFFFF,
		UNDEF_PTR = -1 //0xFFFFFFFF
	};
	uint get_src() const {
		return src_;
		//assert(inds().count(src_));
		//return inds()[src_];
	}
	void set_src(Source* s) {
		if (s->id() > 0xFFFF) {
			cerr << " FUUUUCK! " << s->id() << endl;
			throw std::exception();
		}
		src_ = s->id();
		sys_ = s->sys();
		/*if (srcs().count(id)) {
			src_ = srcs().at(id);
		} else {
			src_ = srcs().size();
			inds().push_back(id);
			srcs()[id] = src_;
		}*/
	}
	//static map<uint, uint>& srcs() { static map<uint, uint> m; return m; }
	//static vector<uint>& inds() { static vector<uint> m; return m; }
	//uint src_:16;
	//uint beg_:24;
	//uint end_:24;


	int sys_;
	int src_;
	int beg_;
	int end_;
};


template<class S>
struct Token {
	typedef S Source;

	Token() { }
	Token(Source* s) : storage(s) { }
	Token(Source* s, const char* b, const char* e) :
	storage(s, b, e) { }

	bool preceeds (const Token<S>& t) {
		if (!src() || !t.src() || t.src() != src()) return false;
		if (t.src()->includes.count(src())) return true;
		if (t.src() == src()) return end() <= t.beg();
		return false;
	}
	bool includes (const Token<S>& t) {
		if (!src() || !t.src() || t.src() != src()) return false;
		return beg() <= t.beg() && t.end() <= end();
	}

	string show(bool full = false) const {
		if (!src()) return "unknown source";
		if (!beg()) return "unknown begin";
		if (!end()) return "unknown end_";
		LocationIter b (src()->data.begin(), src()->id());
		LocationIter e (string::const_iterator(beg()), src()->id());
		LocationIter x = b;
		while (x != e) ++x;
		return full ? "token: " + str() + "\n" + x.loc.show() + "\n" : x.loc.show();
	}
	Location locate() const {
		Location loc(
			src()->id(),
			Source::Sys::ext(),
			Source::Sys::conf(src()->sys()).get("root")
		);
		const char* mid = beg() + length() / 2;
		const char* s = src()->data.c_str();
		while (s) {
			if (*s++ == '\n') { ++loc.line; loc.col = 0; } else ++loc.col;
			if (s == mid) return loc;
		}
		return Location();
	}

	bool is_defined() const { return src() && beg() && end(); }
	operator bool() const { return is_defined(); }
	string str() const { return string(beg(), length()); }
	uint length() const { return beg() <= end() ? end() - beg() : 0; }
	bool operator < (const Token<S>& r) const { return end() <= r.beg(); }

	void set(Source* s, const char* b, const char* e) { storage.set(s, b, e); }
	Source* src() { return storage.src(); }
	const Source* src() const { return storage.src(); }
	const char* beg() const { return storage.beg(); }
	const char* end() const { return storage.end(); }

private:
	TokenStorage<Source> storage;
};


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
		token.beg_ = &string::const_iterator::operator*();
	}
	void end() {
		token.end_ = &string::const_iterator::operator*();
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

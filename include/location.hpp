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
	TokenStorage(const Source* s) : src_(s), beg_(nullptr), end_(nullptr) { }
	TokenStorage(const Source* s, const char* b, const char* e) :
	src_(s), beg_(b), end_(e) { }

	const Source* src() const { return src_; }
	const char* beg() const { return beg_; }
	const char* end() const { return end_; }
	void set(const Source* s, const char* b, const char* e) {
		src_ = s; beg_ = b; end_ = e;
	}
	bool operator < (const TokenStorage& t) const {
		if (src_ < t.src_) return true;
		else if (src_ > t.src_) return false;
		else if (end_ < t.end_) return true;
		else if (end_ > t.end_) return false;
		else return beg_ < t.beg_;
	}
	bool operator == (const TokenStorage& t) const {
		return (src_ == t.src_) && (end_ < t.end_) && (beg_ < t.beg_);
	}
	struct HashCompare {
		static size_t hash(const TokenStorage& s) {
			return reinterpret_cast<size_t>(s.src_) + reinterpret_cast<size_t>(s.beg_) + reinterpret_cast<size_t>(s.end_);
		}
		static bool equal(const TokenStorage& x, const TokenStorage& y) {
			return x.src_ == y.src_ && x.beg_ == y.beg_ && x.end_ == y.end_;
		}
	};

private:
	const Source* src_;
	const char*   beg_;
	const char*   end_;
};

template<class S>
struct TokenStorage<S, TokenType::NONE> {
	typedef S Source;
	TokenStorage() { }
	TokenStorage(const Source* s) { }
	TokenStorage(const Source* s, const char* b, const char* e) { }

	const Source* src() const { return nullptr; }
	const char* beg() const { return nullptr; }
	const char* end() const { return nullptr; }
	void set(const Source* s, const char* b, const char* e) { }

	struct HashCompare {
		static size_t hash(const TokenStorage& s) {
			return 0;
		}
		static bool equal(const TokenStorage& x, const TokenStorage& y) {
			return true;
		}
	};
};

template<class S>
struct TokenStorage<S, TokenType::SEMI> {
	typedef S Source;
	TokenStorage() { }
	TokenStorage(const Source* s) { bits.setSrc(set_src(s)); }
	TokenStorage(const Source* s, const char* b, const char* e) { set(s, b, e); }
	TokenStorage(const TokenStorage& s) : bits(s.bits) { }

	const Source* src() const {
		if (!bits.srcIsDef()) return nullptr;
		Src src = get_src();
		return Source::Sys::get(src.sys_).math.template get<Source>().access(src.src_);
	}
	const char* beg() const {
		return src() ? (bits.begIsDef() ? src()->data().c_str() + bits.beg() : nullptr) : nullptr;
	}
	const char* end() const {
		return src() ? (bits.endIsDef() ? src()->data().c_str() + bits.end() : nullptr) : nullptr;
	}
	void set(const Source* s, const char* b, const char* e) {
		uint src_ = set_src(s);
		assert(b >= s->data().c_str());
		assert(e > s->data().c_str());
		ptrdiff_t beg_ = b - s->data().c_str();
		ptrdiff_t end_ = e - s->data().c_str();
		if (beg_ < 0 || end_ < 0) {
			throw std::length_error("source position can't be less then zero");
		}
		try {
			bits.set(src_, beg_, end_);
		} catch (std::overflow_error& e) {
			throw std::overflow_error(string(e.what()) + "source: " + Lex::toStr(s->id()));
		}
#ifdef DEBUG_LOCATION
		if (s != src()) {
			cerr << "wrong src: " << (void*)s << " != " << (void*)src() << endl;
			throw std::exception();
		}
		if (b != beg()) {
			cerr << "wrong beg: " << (void*)b << " != " << (void*)beg() << endl;
			cerr << "wrong beg: " << string(b, 100) << " != " << string(beg(), 100) << endl;
			cerr << bits.show() << endl;
			throw std::exception();
		}
		if (e != end()) {
			cerr << "wrong end: " << (void*)e << " != " << (void*)end() << endl;
			cerr << "wrong end: " << string(e, 100) << " != " << string(end(), 100) << endl;
			cerr << bits.show() << endl;
			throw std::exception();
		}
#endif
	}
	void operator = (const TokenStorage& s) {
		bits = s.bits;
	}
	bool operator < (const TokenStorage<S>& t) const {
		return bits < t.bits;
	}
	bool operator == (const TokenStorage<S>& t) const {
		return bits == t.bits;
	}
	struct HashCompare {
		static size_t hash(const TokenStorage& s) {
			return s.bits.bits();
		}
		static bool equal(const TokenStorage& x, const TokenStorage& y) {
			return x.bits == y.bits;
		}
	};

private:
	struct Src {
		Src(uint src, uint sys) : src_ (src), sys_(sys) { }
		const uint src_;
		const uint sys_;

		struct HashCompare {
			static size_t hash(const Src& s) {
		        return s.sys_ + s.src_ * (1 << 8);
		    }
		    //! True if strings are equal
		    static bool equal(const Src& x, const Src& y) {
		        return x.src_ == y.src_ && x.sys_ == y.sys_;
		    }
		};
	};

	typedef cmap<Src, uint, typename Src::HashCompare> SrcMap;
	typedef cvector<Src> SrcVector;

	Src get_src() const {
		assert(src_ind()[bits.src()].src_ != -1);
		return src_ind()[bits.src()];
	}
	uint set_src(const Source* s) {
		Src src = Src(s->id(), s->sys());
		typename SrcMap::accessor a;
		if (src_map().insert(a, src)) {
			uint ret = src_map().size();
			src_ind().push_back(src);
			a->second = ret;
		}
		return a->second;
	}
	static SrcMap& src_map() { static SrcMap m; return m; }
	static SrcVector& src_ind() { static SrcVector v; return v; }

	struct Bits {
		Bits() : bits_(UNDEF_ALL) {}
		Bits(const Bits& b) : bits_(b.bits_) { }

		uint src() const { return bits_ & SRC_MASK; }
		uint beg() const { return (bits_ & BEG_MASK) >> 16; }
		uint end() const { return (bits_ & END_MASK) >> (16 + 24) ; }
		std::uint64_t bits() const { return bits_; };

		bool srcIsDef() const { return (bits_ & SRC_MASK) != UNDEF_SRC; }
		bool begIsDef() const { return ((bits_ & BEG_MASK) >> 16) != UNDEF_PTR; }
		bool endIsDef() const { return ((bits_ & END_MASK) >> (16 + 24)) != UNDEF_PTR; }

		void set(uint s, uint b, uint e) {
			if (s >= UNDEF_SRC)
				throw std::overflow_error("number of sources overflow: don't fit into 16 bit unsigned integer\n");
			if (b >= UNDEF_PTR)
				throw std::overflow_error(string("source position ") + to_string(b) + " don't fit into 24 bit unsigned integer\n");
			if (e >= UNDEF_PTR)
				throw std::overflow_error(string("source position ") + to_string(e) + " don't fit into 24 bit unsigned integer\n");
			bits_ = s + ((uint64_t)b << 16) + ((uint64_t)e << (16 + 24));
		}
		void setSrc(uint s) {
			set(s, UNDEF_PTR, UNDEF_PTR);
		}
		void operator = (const Bits& b) {
			bits_ = b.bits_;
		}
		bool operator < (const Bits& b) const {
			return bits_ < b.bits_;
		}
		bool operator == (const Bits& b) const {
			return bits_ == b.bits_;
		}

	private:
		enum {
			UNDEF_ALL = (uint64_t)0xFFFFFFFFFFFFFFFF,    // 64 bits
			UNDEF_SRC = (uint64_t)0xFFFF,                // 16 bits
			UNDEF_PTR = (uint64_t)0xFFFFFF,              // 24 bits
			SRC_MASK  = (uint64_t)0xFFFF,                // first 16 bits
			BEG_MASK  = (uint64_t)0xFFFFFF << 16,        // following 24 bits
			END_MASK  = (uint64_t)0xFFFFFF << (16 + 24), // following 24 bits
		};
		std::uint64_t bits_;
	};

	Bits bits;
};

template<class S>
struct Token {
	typedef S Source;
	typedef TokenStorage<Source> Storage;

	Token() { }
	Token(const Source* s) : storage(s) { }
	Token(const Source* s, const char* b, const char* e) : storage(s, b, e) { }
	Token(const Token& t) : storage(t.storage) { }

	bool preceeds (const Token<S>& t) const {
		if (!src() || !t.src()) return false;
		if (t.src()->includes(src())) return true;
		if (t.src() == src()) return end() <= t.beg();
		return false;
	}
	bool includes (const Token<S>& t) const {
		if (!src() || !t.src() || t.src() != src()) return false;
		return beg() <= t.beg() && t.end() <= end();
	}

	string show(bool full = false) const {
		if (!src()) return "unknown source";
		if (!beg()) return "unknown begin";
		if (!end()) return "unknown end_";
		LocationIter b (src()->data().begin(), src()->id());
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
		const char* s = src()->data().c_str();
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
	bool operator < (const Token<S>& r) const {
		return storage < r.storage;
	}
	bool operator == (const Token<S>& r) const {
		return storage == r.storage;
	}
	void operator = (const Token& t) {
		storage = t.storage;
	}

	void set(Source* s, const char* b, const char* e) { storage.set(s, b, e); }
	const Source* src() const { return storage.src(); }
	const char* beg() const { return storage.beg(); }
	const char* end() const { return storage.end(); }

	struct HashCompare {
		static size_t hash(const Token& t) {
			return Storage::HashCompare::hash(t.storage);
		}
		static bool equal(const Token& x, const Token& y) {
			return Storage::HashCompare::equal(x.storage, y.storage);
		}
	};

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
	virtual const Tokenable* ref() const { return nullptr; }
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

template<class S>
inline ostream& operator << (ostream& os, const Token<S>& t) {
	os << t.str();
	return os;
}

} 

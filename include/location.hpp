#pragma once

#include "std.hpp"
#include "lex.hpp"
#include "xml.hpp"

namespace mdl { 

struct Indent {
	int  num;
	char del;

	Indent(int n = 0, char d = '\t') : num(n), del(d) {
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
	static string paragraph(const string& str, int d) {
		Indent ind(d);
		return paragraph(str, ind.str());
	}
	string str() const {
		string s;
		int n = num;
		while (n--) s += del;
		return s;
	}
	Indent operator + (int k) const {
		return Indent(num + k, del);
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
		s += "line: " + to_string(line + 1) + " ";
		s += "col: "  + to_string(col + 1) + " ";
		s += "path: " + root + "/" + Lex::toStr(file) + "." + ext + " ";
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
	LocationIter() = default;
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

enum class TokenType { FULL, SMALL, TINY, DEFAULT = TINY };
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
		return (src_ == t.src_) && (end_ == t.end_) && (beg_ == t.beg_);
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
struct TokenStorage<S, TokenType::SMALL> {
	typedef S Source;
	TokenStorage() : src_(nullptr), beg_(-1), end_(-1) { }
	TokenStorage(const Source* s) : src_(s), beg_(-1), end_(-1) { }
	TokenStorage(const Source* s, const char* b, const char* e) :
	src_(s), beg_(s ? (b ? b - src_beg() : -1) : -1), end_(s ? (e ? e - src_beg() : -1) : -1) { }

	const Source* src() const { return src_; }
	const char* beg() const { return src_ ? (beg_ == -1 ? nullptr : src_beg() + beg_) : nullptr; }
	const char* end() const { return src_ ? (end_ == -1 ? nullptr : src_beg() + end_) : nullptr; }
	void set(const Source* s, const char* b, const char* e) {
		src_ = s;
		if (src_) {
			beg_ = b ? b - src_beg() : -1;
			end_ = e ? e - src_beg() : -1;
		} else {
			beg_ = -1;
			end_ = -1;
		}
	}
	bool operator < (const TokenStorage& t) const {
		if (src_ < t.src_) return true;
		else if (src_ > t.src_) return false;
		else if (end_ < t.end_) return true;
		else if (end_ > t.end_) return false;
		else return beg_ < t.beg_;
	}
	bool operator == (const TokenStorage& t) const {
		return (src_ == t.src_) && (end_ == t.end_) && (beg_ == t.beg_);
	}
	struct HashCompare {
		static size_t hash(const TokenStorage& s) {
			return reinterpret_cast<size_t>(s.src_) + s.beg_ + s.end_;
		}
		static bool equal(const TokenStorage& x, const TokenStorage& y) {
			return x.src_ == y.src_ && x.beg_ == y.beg_ && x.end_ == y.end_;
		}
	};

private:
	const char* src_beg() const { return src_->data().c_str(); }
	const Source* src_;
	std::uint32_t beg_;
	std::uint32_t end_;
};

template<class S>
struct TokenStorage<S, TokenType::TINY> {
	typedef S Source;
	TokenStorage() = default;
	TokenStorage(const Source* s) {
		if (s) {
			//bits.setSrc(resolve_src(s));
			bits.set(resolve_src(s), 0, 0);
		}
	}
	TokenStorage(const Source* s, const char* b, const char* e) {
		if (s) {
			try {
				bits.set(resolve_src(s), b - src_beg(s), e -b);
			} catch (std::overflow_error& ex) {
				string msg = ex.what();
				msg += "source: " + Lex::toStr(s->id()) + ", beg: " + string(b, 32) + "\n";
				cout << msg << endl;
				throw std::overflow_error(msg);
			}
		}
	}
	TokenStorage(const TokenStorage& ts) : bits(ts.bits) { }

	const Source* src() const { return bits.srcIsDef() ? return_src(bits.src()) : nullptr; }
	const char* beg() const { return bits.srcIsDef() ? (bits.begIsDef() ? src_beg(src()) + bits.beg() : nullptr) : nullptr; }
	const char* end() const { return bits.srcIsDef() ? (bits.endIsDef() ? src_beg(src()) + bits.end() : nullptr) : nullptr; }
	void set(const Source* src, const char* b, const char* e) {
		uint s = resolve_src(src);
		bits.setSrc(s);
		if (src) {
			try {
				bits.set(s, b ? b - src_beg(src) : Bits::UNDEF_BEG, (e && b) ? e - b : Bits::UNDEF_LEN);
			} catch (std::overflow_error& ex) {
				string msg = ex.what();
				msg += "source: " + Lex::toStr(src->id()) + ", beg: " + string(b, 32) + "\n";
				cout << msg << endl;
				throw std::overflow_error(msg);
			}
		}
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
	typedef cmap<const Source*, uint> SourceMap;
	typedef cmap<uint, const Source*> IndMap;
	uint resolve_src(const Source* s) {
		if (s == nullptr) {
			return Bits::UNDEF_SRC;
		}
		uint src = -1;
		typename SourceMap::accessor a;
		if (src_map().insert(a, s)) {
			src = counter()++;
			typename IndMap::accessor b;
			if (ind_map().insert(b, src)) {
				b->second = s;
			} else {
				throw std::runtime_error("Token::resolve_src - ind_map already has value, while it shouldn't");
			}
			a->second = src;
		} else {
			src = a->second;
		}
		return src;
	}
	const Source* return_src(uint s) const {
		if (s == Bits::UNDEF_SRC) {
			return nullptr;
		}
		const Source* src = nullptr;
		typename IndMap::const_accessor a;
		if (ind_map().find(a, s)) {
			src = a->second;
		}
		return src;
	}
	static const char* src_beg(const Source* s) { return s ? s->data().c_str() : nullptr; }
	static SourceMap& src_map() { static SourceMap src_map_; return src_map_; }
	static IndMap& ind_map() { static IndMap src_vect_; return src_vect_; }
	static std::atomic<uint>& counter() { static std::atomic<uint> counter_(0); return counter_; }

	struct Bits {
		Bits() : bits_(UNDEF_ALL) {}
		Bits(const Bits& b) : bits_(b.bits_) { }

		uint src() const { return bits_ & SRC_MASK; }
		uint beg() const { return (bits_ & BEG_MASK) >> 16; }
		uint len() const { return (bits_ & LEN_MASK) >> (16 + 32) ; }
		uint end() const { return beg() + len(); }
		std::uint64_t bits() const { return bits_; };

		bool srcIsDef() const { return (bits_ & SRC_MASK) != UNDEF_SRC; }
		bool begIsDef() const { return ((bits_ & BEG_MASK) >> 16) != UNDEF_BEG; }
		bool lenIsDef() const { return ((bits_ & LEN_MASK) >> (16 + 32)) != UNDEF_LEN; }
		bool endIsDef() const { return begIsDef() && lenIsDef(); }

		void set(uint s, uint b, uint l) {
			if (s > UNDEF_SRC) {
				throw std::overflow_error("number of sources overflow: " + to_string(s) + " don't fit into 16 bit unsigned integer\n");
			}
			if (b > UNDEF_BEG) {
				throw std::overflow_error("source position " + to_string(b) + " don't fit into 32 bit unsigned integer\n");
			}
			if (l > UNDEF_LEN) {
				//throw std::overflow_error("source position length " + to_string(l) + " don't fit into 16 bit unsigned integer\n");
				l = UNDEF_LEN - 1;
			}
			bits_ = s + ((uint64_t)b << 16) + ((uint64_t)l << (16 + 32));
		}
		void setSrc(uint s) {
			set(s, UNDEF_BEG, UNDEF_LEN);
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
		enum {
			UNDEF_ALL = (uint64_t)0xFFFFFFFFFFFFFFFF,    // 64 bits
			UNDEF_SRC = (uint64_t)0xFFFF,                // 16 bits
			UNDEF_BEG = (uint64_t)0xFFFFFFFF,            // 32 bits
			UNDEF_LEN = (uint64_t)0xFFFF,                // 16 bits
			SRC_MASK  = (uint64_t)0xFFFF,                // first 16 bits
			BEG_MASK  = (uint64_t)0xFFFFFFFF << 16,      // following 32 bits
			LEN_MASK  = (uint64_t)0xFFFFFF << (16 + 32), // following 16 bits
		};
	private:
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

	bool preceeds(const Token<S>& t) const {
		if (!src() || !t.src()) return false;
		if (t.src()->includes(src())) return true;
		if (t.src() == src()) return end() <= t.beg();
		return false;
	}
	bool includes(const Token<S>& t) const {
		if (!src() || !t.src() || t.src() != src()) return false;
		return beg() <= t.beg() && t.end() <= end();
	}
	bool includes(const char* pos) const {
		if (!src()) return false;
		return beg() <= pos && pos <= end();
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
	string showRaw() const {
		if (!src()) return "unknown source";
		if (!beg()) return "unknown begin";
		if (!end()) return "unknown end_";
		string ret;
		ret += "src: " + Lex::toStr(src()->id()) + "\n";
		ret += "beg: " + string(beg(), 1) + "\n";
		ret += "end: " + string(end(), 1) + "\n";
		return ret;
	}
	Location locate() const {
		if (!src() || !beg() || !end()) {
			return Location();
		}
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

	void set(Source* s, const char* b = nullptr, const char* e = nullptr) { storage.set(s, b, e); }
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
struct Id {
	typedef S Sys;
	Id(uint i = -1, uint s = -1) : id_(i), sys_(s == -1 ? Sys::get().id : s) { }
	Id(const Id& i) = default;

	string str() const { return Lex::toStr(id_); }
	uint sys() const { return sys_; }
	uint id() const { return id_; }

protected:
	void set(uint i, uint s) { sys_ = s; id_ = i; }
	void drop() { sys_ = -1; id_ = -1; }

private:
	uint id_;
	uint sys_;
};

template<class S>
struct WithToken {
	WithToken(const Token<S>& t) : token(t) { }
	WithToken(const WithToken&) = default;

	Token<S> token;
};

template<class S>
struct TokenId : public Token<S>, public Id<S> {
	TokenId(uint i, const Token<S>& t = Token<S>()) :
		Token<S>(t), Id<S>(i) { }
	TokenId(const TokenId&) = default;
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
		token_.beg_ = &string::const_iterator::operator*();
	}
	void end() {
		token_.end_ = &string::const_iterator::operator*();
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
	while (src && *src != '\0') {
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

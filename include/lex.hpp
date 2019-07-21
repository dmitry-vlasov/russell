#pragma once

#include "std.hpp"

namespace mdl {

struct Lex {
	static uint getInt(const string& str) { return get().getIndex(str); }
	static uint toInt(const string& str) { return get().toIndex(str); }
	static string toStr (uint i) { return get().toString(i); }
	static bool isDef(uint i) { Back::const_accessor a; return get().back.find(a, i); }
	static bool isDef(const string& str) { There::const_accessor a; return get().there.find(a, str);  }

private:
	typedef cmap<string, uint> There;
	typedef cmap<uint, string> Back;
	Lex() : counter(0) { }

	static Lex& get() { static Lex lex; return lex; }
	uint getIndex(const string& str) const {
		There::const_accessor a;
		return there.find(a, str) ? a->second : -1;
	}
	uint toIndex(const string& str) {
		There::accessor a;
		if (there.insert(a, str)) {
			uint i = counter++;
			a->second = i;
			Back::accessor b;
			back.insert(b, i);
			b->second = str;
		}
		return a->second;
	}
	string toString(uint i) const {
		Back::const_accessor b;
		return back.find(b, i) ? b->second : "<UNDEF>";
	}

	There there;
	Back  back;
	atomic<uint> counter;
};

inline string show_id(uint lab) {
	return Lex::toStr(lab);
}

} // mdl

  

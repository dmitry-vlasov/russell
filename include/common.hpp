#pragma once

#include "std.hpp"
#include "location.hpp"
#include "error.hpp"
#include "table.hpp"
#include "timer.hpp"
#include "expr.hpp"

#define VERSION "0.2"

namespace mdl {

template<
	class Key,
	class T,
	class Compare = std::less<Key>,
	class Alloc = std::allocator<pair<const Key,T>>
>
struct Map {
	map<Key, T, Compare, Alloc> m;
	bool has(Key k) const {
		return m.find(k) != m.end();
	}
	T& operator[] (Key k) {
		return m[k];
	}
	T operator[] (Key k) const {
		return m.find(k)->second;
	}
};

template<
	class T,
	class Compare = std::less<T>,
	class Alloc = std::allocator<T>
>
struct Set {
	set<T, Compare, Alloc> s;
	bool has(T val) const {
		return s.find(val) != s.end();
	}
};

class indent {
	int  num;
	char del;
public:
	indent(int n = 1, char d = '\t') : num(n), del(d) {
	}
	void write(ostream& os) {
		while (num --) os << del;
	}
	static string paragraph(const string& str, string d = "\t") {
		string indented;
		for (char ch : str) {
			if (ch == '\n') indented += "\n" + d;
			else            indented += ch;
		}
		return indented;
	}
};

inline ostream& operator << (ostream& os, indent ind) {
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

template<typename T>
void join(vector<T>& v1, const vector<T>& v2) {
	for (auto p : v2) v1.push_back(p);
}

template<class T>
size_t memvol(const T& x) {
	return 0;
}

template<class T>
size_t memsize(const T& x) {
	return sizeof(T) + memvol(x);
}

}

  

#pragma once

#include "std.hpp"
#include "location.hpp"
#include "timer.hpp"
#include "expr.hpp"

#define VERSION "0.2"

namespace mdl {

inline bool undef(uint x) { return x == (uint)-1; }

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
	T operator[] (Key k) const;
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

class Table {
	vector<string> strings;
	map<string, uint> table;
public:
	Table() : strings(), table() { }
	uint getInt(const string& str) const {
		if (table.find(str) == table.end())
			return -1;
		else
			return table.find(str)->second;
	}
	uint toInt(const string& str) {
		if (table.find(str) == table.end()) {
			int ind = table.size();
			table[str] = ind;
			strings.push_back(str);
		}
		return table[str];
	}
	const string& toStr (uint i) const {
		if (i >= strings.size()) {
			static string str = "<UNDEF>";
			return str;
		}
		return strings[i];
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

template<class T>
size_t memvol(const Map<uint, T*>& map) {
	size_t vol = 0;
	for (auto& p : map.m) {
		vol += memsize(*p.second);
	}
	return vol;
}

namespace mem {
	enum Units {
		KB = 1024,
		MB = KB * 1024,
		GB = MB * 1024
	};
}

inline string showmem(size_t s) {
	const uint gb =  s / mem::GB;
	const uint mb = (s - gb * mem::GB) / mem::MB;
	const uint kb = (s - gb * mem::GB - mb * mem::MB) / mem::KB;
	const uint  b =  s - gb * mem::GB - mb * mem::MB - kb * mem::KB;

	     if (gb) return to_string(gb) + " gb " + to_string(mb) + " mb";
	else if (mb) return to_string(mb) + " mb " + to_string(kb) + " kb";
	else if (kb) return to_string(kb) + " kb " + to_string(b)  + " b";
	else         return to_string(b)  + " b";
}

class Error : public std::exception {
public :
	virtual ~Error() { }

	void location(const Location& loc) {
		msg += "\nat: " + show(loc);
	}
	Error (const string& str, const Location* loc = nullptr) throw() :
	msg() {
		msg += "error: " + str;
		if (loc) location(*loc);
		msg += "\n";
	}
	Error (const string& str, const string& s, const Location* loc = nullptr) throw() :
	msg() {
		msg += "error: " + str + " : " + s;
		if (loc) location(*loc);
		msg += "\n";
	}
	virtual const char* what() const throw() {
		return msg.c_str();
	}
	string   msg;
};

template<class Key, class T, class Compare, class Alloc>
T Map<Key, T, Compare, Alloc>::operator[] (Key k) const {
	if (has(k))
		return m.find(k)->second;
	else
		throw Error("map doesn't have an element");
}

inline string cut_outer_directory(string path) {
	size_t slash_pos = path.find_first_of("/");
	return path.substr(slash_pos == string::npos ? 0 : slash_pos + 1);
}

ifstream open_smart(string& path, string root = "");

template<class T>
void deep_write(T* target, auto (get_cont)(T*), T* (get_inc)(auto), bool (is_inc)(auto)) {
	typedef T Source;
	namespace fs = boost::filesystem;
	Set<Source*> written;
	stack<Source*> to_write;
	to_write.push(target);
	while (!to_write.empty()) {
		Source* src = to_write.top();
		if (!fs::exists(src->dir()))
			fs::create_directories(src->dir());
		ofstream out(src->path());
		out << *src << endl;
		out.close();
		written.s.insert(src);
		to_write.pop();
		for (auto n : get_cont(src)) {
			if (is_inc(n)) {
				Source* inc = get_inc(n);
				if (!written.has(inc)) {
					to_write.push(inc);
				}
			}
		}
	}
}

}

  

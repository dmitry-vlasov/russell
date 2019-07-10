#pragma once

#include <numeric>
#include <cmath>

#include "std.hpp"

namespace mdl {

template<class T>
struct maybe_deleter {
	explicit maybe_deleter(bool doit = true) : _delete(doit) { }

	void operator() (T* p) const{
		if (_delete) delete p;
	}
private:
	bool _delete;
};

template<class T>
using set_unique_ptr = std::unique_ptr<T, maybe_deleter<T>>;

template<class T>
set_unique_ptr<T> make_find_ptr(T* raw){
	return set_unique_ptr<T>(raw, maybe_deleter<T>(false));
}

template<class T>
uint find_in_vector(const vector<unique_ptr<T>>& pv, const T* pn) {
	uint i = 0;
	for (auto& p : pv) {
		if (p.get() == pn) {
			return i;
		}
		++i;
	}
	return -1;
}

template<class T>
uint find_in_vector(const vector<T*>& pv, const T* pn) {
	uint i = 0;
	for (auto& p : pv) {
		if (p == pn) {
			return i;
		}
		++i;
	}
	return -1;
}

template<class T>
vector<T> unite_sorted(const vector<T>& right, const vector<T>& left) {
	vector<T> ret(right.size() + left.size());
	auto end = std::merge(right.begin(), right.end(), left.begin(), left.end(), ret.begin());
	ret.resize(end - ret.begin());
	return ret;
}

template<class T>
bool sets_intersect(const set<T>& right, const set<T>& left) {
	for (const T& t : right) {
		if (left.count(t)) {
			return true;
		}
	}
	return false;
}

template<class T>
set<T> sets_intersection(const set<T>& right, const set<T>& left) {
	set<T> ret;
	for (const T& t : right) {
		if (left.count(t)) {
			ret.insert(t);
		}
	}
	return ret;
}

template<class T>
set<T> sets_union(const set<T>& right, const set<T>& left) {
	set<T> ret;
	for (const T& t : right) {
		ret.insert(t);
	}
	for (const T& t : left) {
		ret.insert(t);
	}
	return ret;
}

template<class T1, class T2>
vector<T1> map_keys(const map<T1, T2>& m) {
	vector<T1> ret;
	for (const auto& p : m) {
		ret.push_back(p.first);
	}
	return ret;
}

template<class T1, class T2>
vector<T2> map_values(const map<T1, T2>& m) {
	vector<T2> ret;
	for (const auto& p : m) {
		ret.push_back(p.second);
	}
	return ret;
}

// Average
template<typename T>
double avg(const vector<T>& v) {
	return std::accumulate(v.begin(), v.end(), 0.0, [](T s, T a) { return a + s; }) / v.size();
}

// Standard deviation
template<typename T>
double stdev(const vector<T>& v) {
	double a = avg(v);
	return sqrt(std::accumulate(v.begin(), v.end(), 0.0, [a](T s, T t) { return s + (t - a) * (t - a); }) / v.size());
}

template<typename T>
T vect_min(const vector<T>& v) {
	return std::accumulate(v.begin(), v.end(), std::numeric_limits<T>::max(), [](T t, T a) { return std::min(a, t); });
}

template<typename T>
T vect_max(const vector<T>& v) {
	return std::accumulate(v.begin(), v.end(), std::numeric_limits<T>::min(), [](T t, T a) { return std::max(a, t); });
}

template<class T> struct Undef;
template<> struct Undef<uint> {
	static uint get()        { return -1; }
	static bool is(uint x)   { return x == -1; }
	static void set(uint& x) { x = -1; }
};

template<class T> struct Undef<T*> {
	static T*   get()      { return nullptr; }
	static bool is(T* x)   { return x == nullptr; }
	static void set(T*& x) { x = nullptr;  }
};

template<typename T>
void join(vector<T>& v1, const vector<T>& v2) {
	for (auto p : v2) v1.push_back(p);
}

template<class T>
void dump(const T& val) { cout << val; }

template<class D>
inline string shower(const D&) { return ""; }

template<class T>
void show_vector(const vector<T>& v, ostream& os, const string& delim = ", ") {
	if (v.size()) {
		os << v.at(0);
		for (uint i = 1; i < v.size(); ++i) {
			os << delim << v.at(i);
		}
	}
}

template<class T>
string show_vector(const vector<T>& v, const string& delim = ", ") {
	ostringstream oss;
	show_vector(v, oss, delim);
	return oss.str();
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
size_t memvol(const map<uint, T*>& map) {
	size_t vol = 0;
	for (auto& p : map) {
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

inline string trim_string(const string& str, const string& symbs_to_remove) {
	//cout << "to trim: " << str << " with: " << symbs_to_remove << endl;
	string::size_type beg = str.find_first_not_of(symbs_to_remove);
	string::size_type end = str.find_last_not_of(symbs_to_remove);
	if (beg != string::npos) {
	auto ret = str.substr(beg, end - beg + 1);
		//cout << "trimmed: " << ret << endl;
		return ret;
	} else {
		return "";
	}
}

inline string glue_string(const vector<string>& arr, const string& delim) {
	string ret;
	if (arr.size()) {
		ret += arr.at(0);
		for (uint i = 1; i < arr.size(); ++i) {
			ret += delim + arr.at(i);
		}
	}
	return ret;
}

inline vector<string> split_string(const string& str, const string& delim) {
	//cout << "to split: '" << str << "', delim: " << delim << endl;
	vector<string> ret;
	string::size_type pos = 0;
	while (pos != string::npos) {
		uint old_pos = pos;
		pos = str.find(delim, pos);
		ret.emplace_back(str.substr(old_pos, pos));
		if (pos != string::npos) {
			pos += delim.length();
		}
	}
	//cout << "splited: '" << glue_string(ret, "---") << "'" << endl;
	return ret;
}

} // mdl

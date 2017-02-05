#pragma once

#include "std.hpp"
#include "location.hpp"
#include "symbol.hpp"
#include "timer.hpp"

namespace mdl {

template<class T> struct Undef;
template<> struct Undef<uint> {
	static uint get()        { return UNDEF_UINT; }
	static bool is(uint x)   { return x == UNDEF_UINT; }
	static void set(uint& x) { x = UNDEF_UINT; }
};

template<class T> struct Undef<T*> {
	static T*   get()      { return nullptr; }
	static bool is(T* x)   { return x == nullptr; }
	static void set(T*& x) { x = nullptr;  }
};

struct Table {
	typedef map<string, uint> Table_;
	typedef vector<string> Strings_;
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
	Strings_ strings;
	Table_   table;
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

inline string cut_outer_directory(string path) {
	size_t slash_pos = path.find_first_of("/");
	return path.substr(slash_pos == string::npos ? 0 : slash_pos + 1);
}

ifstream open_smart(string& path, string root);
void read_smart(string& data, ifstream&);

template<class T>
void deep_write(T* target, auto get_cont, auto get_inc, auto is_inc) {
	typedef T Source;
	namespace fs = boost::filesystem;
	set<Source*> written;
	stack<Source*> to_write;
	to_write.push(target);
	while (!to_write.empty()) {
		Source* src = to_write.top();
		if (!fs::exists(src->dir()))
			fs::create_directories(src->dir());
		ofstream out(src->path());
		out << *src << endl;
		out.close();
		written.insert(src);
		to_write.pop();
		for (auto n : get_cont(src)) {
			if (is_inc(n)) {
				Source* inc = get_inc(n);
				if (!written.count(inc)) {
					to_write.push(inc);
				}
			}
		}
	}
}

template<class Source, class Parser>
void parse(Source*& src, string& data, auto space) {
	LocationIter iter(data.begin(), src->name);
	LocationIter end(data.end(), src->name);
	if (!Parser::parse(iter, end, space, *src) || iter != end) {
		throw Error("parsing failed", src->name);
	}
}

template<class Source, class Parser>
Source* parse(string name, string root, auto space) {
	ifstream in = open_smart(name, root);
	Source* src = new Source(root, name);
	read_smart(src->data, in);
	parse<Source, Parser>(src, src->data, space);
	return src;
}

template<class Source, class Parser, class Inclusion>
Inclusion* include(string path, string root, auto space, Source* (get_src)(Inclusion*)) {
	static map<string, Inclusion*> included;
	if (included.count(path)) {
		Inclusion* inc = included[path];
		return new Inclusion(get_src(inc), false);
	} else {
		//cout << "parsing src: " << path << endl;
		string data;
		string orig_path(path);
		ifstream in = open_smart(path, root);
		Source* src = new Source(root, path);
		read_smart(src->data, in);

		Inclusion* inc = new Inclusion(src, true);
		included[orig_path] = inc;
		parse<Source, Parser>(src, src->data, space);
		return inc;
	}
}

// Library, singleton, which contains a variety of deductive systems
template<typename T>
struct Lib {
	typedef T System;
	static const Lib& get() { return mod(); }
	static Lib& mod() { static Lib lib; return lib; }

	System& sys() { return systems[current]; }

	map<string, System> systems;
	string current;

private:
	Lib() : systems(), current() { }
};

// Configuration for a deductive system
template<typename M, typename T>
struct Config {
	typedef M Mode;
	typedef T Target;
	Config() :
	verbose(false), info(false), help(false), deep(false),
	mode(Mode::DEFAULT), in(), root(), target(Target::DEFAULT) { }

	bool verbose;
	bool info;
	bool help;
	bool deep;

	Mode mode;

	string in;
	string out;
	string root;
	Target target;
};

} // mdl

  

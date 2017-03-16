#pragma once

#include <boost/program_options.hpp>

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

struct Lex {
	static uint getInt(const string& str) { return get().getIndex(str); }
	static uint toInt(const string& str) { return get().toIndex(str); }
	static const string& toStr (uint i) { return get().toString(i); }

private:
	Lex() : strings(), table() { }
	static Lex& get() { static Lex lex; return lex; }
	uint getIndex(const string& str) const {
		if (table.find(str) == table.end())
			return -1;
		else
			return table.find(str)->second;
	}
	uint toIndex(const string& str) {
		if (table.find(str) == table.end()) {
			int ind = table.size();
			table[str] = ind;
			strings.push_back(str);
		}
		return table[str];
	}
	const string& toString(uint i) const {
		if (i >= strings.size()) {
			static string str = "<UNDEF>";
			return str;
		}
		return strings[i];
	}
	vector<string>    strings;
	map<string, uint> table;
};

inline string show_sy(Symbol symb) {
	return Lex::toStr(symb.lit);
}
inline string show_id(uint lab) {
	return Lex::toStr(lab);
}

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

template<class T>
void shallow_write(T* target) {
	typedef T Source;
	namespace fs = boost::filesystem;
	string dir = target->dir();
	if (!dir.empty() && !fs::exists(dir))
		fs::create_directories(dir);
	ofstream out(target->path());
	out << *target << endl;
	out.close();
}

struct Path {
	Path() : root(), name(), ext() { }
	Path(const string& n, const string& r, const string& e) : root(r), name(n), ext(e) {
		boost::trim(root);
		boost::trim(name);
		boost::erase_last(root, "/");
		boost::trim(ext);
	}
	Path(const string& n, const string& r = "") : root(r), name(), ext() {
		boost::trim(root);
		boost::trim(name);
		boost::erase_last(root, "/");
		name_ext(n);
	}
	Path(const Path& p) : root(p.root), name(p.name), ext(p.ext) { }
	Path& operator = (const Path& p) {
		root = p.root;
		name = p.name;
		ext = p.ext;
		return *this;
	}
	string path() const {
		return (root.size() ? root + "/" : "") + name + (ext.size() ? "." + ext : "");
	}
	string dir() const {
		string p = path();
		int i = p.find_last_of("/");
		return (i == string::npos) ? "" : p.substr(0, i) + "/";
	}
	void name_ext(string ne) {
		boost::trim(ne);
		int i = ne.find_last_of(".");
		name = ne.substr(0, i);
		ext.clear();
		if (i != string::npos) ext = ne.substr(i + 1);
	}
	void read(string& data) const {
		ifstream in(path());
		in.unsetf(std::ios::skipws);
		std::copy(
			std::istream_iterator<char>(in),
			std::istream_iterator<char>(),
			std::back_inserter(data));
		in.close();
	}
	void write(const string& data) const {
		ofstream out(path());
		std::copy(
			data.begin(),
			data.end(),
			std::ostream_iterator<char>(out));
		out.close();
	}
	Path relative(const string& n) const {
		return Path(n, root, ext);
	}
	string root;
	string name;
	string ext;
};

// Library, singleton, which contains a variety of deductive systems
template<typename T>
struct Lib {
	static const Lib& get() { return mod(); }
	static Lib& mod() { static Lib lib; return lib; }

	void init(const string& curr) {
		current = curr;
		contents[current].reset(new T());
	}
	template<class TR>
	void init(const string& curr) {
		current = curr;
		contents[current].reset(new TR());
	}

	T& access() {
		assert(contents.count(current));
		return *contents[current];
	}
	template<class TR>
	T& access() {
		assert(contents.count(current));
		return *contents[current];
	}
	string current;

private:
	map<string, unique_ptr<T>> contents;
	Lib() : contents(), current("default") { }
};

enum class Lang { NONE, MM, SMM, RUS, DEFAULT = NONE };
enum class Mode { NONE, TRANSL, CUT, MERGE, PROVE, DEFAULT = NONE };

// Configuration for a deductive system
struct Conf {
	Conf() :
	verbose(false), info(false), help(false), deep(false),
	in(), out(),
	mode(Mode::DEFAULT), target(Lang::DEFAULT) { }

	bool verbose;
	bool info;
	bool help;
	bool deep;

	Path in;
	Path out;

	Mode mode;
	Lang target;
};

struct Io {
	virtual ~Io() { };
	virtual ostream& out() = 0;
	virtual ostream& err() = 0;
	struct Std;
};

struct Io::Std : public Io {
	virtual ~Std() { };
	ostream& out() override { return cout; }
	ostream& err() override { return cerr; }
};

struct Return {
	Return(const string& t = "", bool s = true, any d = any()) : text(t), data(d), success(s) { }
	string text;
	any    data;
	bool   success;
};

typedef vector<string> Args;
typedef map<string, Timer> Timers;
typedef function<Return (const Args&)> Action;

// Template for a deductive system
template<class S, class M>
struct Sys {
	typedef S System;
	typedef M Math;

	Timers timers;
	Conf   config;
	Math   math;
	map<string, Action> action;

	static const System& get() { return mod(); }
	static System& mod()   { return Lib<System>::mod().access();  }
	static Io& io()        { return Lib<Io>::mod().access();  }
	static Timers& timer() { return mod().timers;  }
	static Conf& conf()    { return mod().config;  }

	static void change(const string& name) {
		if (!instances().count(name)) throw Error("no such sys instance");
		Lib<System>::mod().current = name;
		Lib<Io>::mod().current = name;
	}
	template<class IO = Io::Std>
	static void init(const string& name = "default") {
		if (instances().count(name)) throw Error("sys instance already initialized");
		instances().insert(name);
		Lib<Io>::mod().init<IO>(name);
		Lib<System>::mod().init(name);
	}

private:
	static set<string> instances() { static set<string> inst; return inst; }
};

template<class T>
string show_timer(const char* message, const string& name, const T& timers) {
	return timers.count(name) ? string(message) + show(timers.at(name)) : "";
}

template<class T>
void dump(const T& val) { cout << val; }

template<class D>
struct Table {
	typedef D Data;
	void add(uint n, Data* p = nullptr) {
		if (!refs.count(n)) {
			refs[n].data = p;
		} else {
			Storage& d = refs[n];
			if (d.data) throw Error("attempt to reuse live pointer");
			d.data = p;
			for (Data** u : d.users) *u = p;
		}
	}
	void del(uint n) {
		if (!refs.count(n)) throw Error("attempt to delete unknown label");
		Storage& d = refs[n];
		if (!d.data) throw Error("attempt to delete null pointer");
		d.data = nullptr;
		for (Data** u : d.users) *u = nullptr;
	}
	void use(uint n, Data*& u) {
		if (!refs.count(n)) throw Error("attempt to use unknown label");
		Storage& d = refs[n];
		if (!d.data) throw Error("attempt to use null pointer");
		d.users.insert(&u);
		u = d.data;
	}
	void unuse(uint n, Data*& u) {
		if (!refs.count(n)) throw Error("attempt to unuse unknown label");
		Storage& d = refs[n];
		d.users.erase(&u);
	}
	Data* access(uint n) {
		return refs.count(n) ? refs.at(n).data : nullptr;
	}
	const Data* access(uint n) const {
		return refs.count(n) ? refs.at(n).data : nullptr;
	}
	bool has(uint n) const {
		return refs.count(n);
	}
	void destroy() {
		for (auto p : refs) delete p.second.data;
	}
	int size() const { return refs.size(); }

private :
	struct Storage {
		Data* data;
		set<Data**> users;
	};
	map<uint, Storage> refs;
};


} // mdl

  

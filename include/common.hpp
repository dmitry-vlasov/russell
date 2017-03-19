#pragma once

#include "std.hpp"
#include "location.hpp"
#include "symbol.hpp"
#include "timer.hpp"
#include "actions.hpp"
#include "lex.hpp"
#include "error.hpp"

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

template<class T>
void deep_write(const T* target, auto get_cont, auto get_inc, auto is_inc) {
	typedef T Source;
	namespace fs = boost::filesystem;
	set<const Source*> written;
	stack<const Source*> to_write;
	to_write.push(target);
	while (!to_write.empty()) {
		const Source* src = to_write.top();
		if (!fs::exists(src->dir()))
			fs::create_directories(src->dir());
		ofstream out(src->path().path());
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
	ofstream out(target->path().path());
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

struct Timers {
	Timer& operator[] (const string& s) { return timers[s]; }
	const Timer& operator[] (const string& s) const { return timers.at(s); }
	string show() const;
	map<string, Timer> timers;
};

// Template for a deductive system
template<class S, class M>
struct Sys {
	typedef S System;
	typedef M Math;

	Timers timers;
	Conf   config;
	Math   math;
	map<string, Function> action;

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
string show_timer(const char* message, const string& name, const T& t) {
	return t.timers.count(name) ? string(message) + show(t.timers.at(name)) : "";
}

template<class T>
void dump(const T& val) { cout << val; }

template<class D>
struct Table {
	typedef D Data;

private:
	struct Storage {
		Data* data;
		set<Data**> users;
	};
	map<uint, Storage> refs;

public:
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

	typedef typename map<uint, Storage>::iterator iterator;
	typedef typename map<uint, Storage>::const_iterator const_iterator;

	iterator begin() { return refs.begin(); }
	iterator end() { return refs.end(); }

	const_iterator cbegin() const { return refs.cbegin(); }
	const_iterator cend() const { return refs.cend(); }
};

template<class Src, class Sys>
struct Source {
	Source(uint l) : label(l) { }

	uint      label;
	string    data;
	set<Src*> deps;

	Path path() const { return Sys::conf().in.relative(name()); }
	string name() const { return Lex::toStr(label); }
	string dir() const { return path().dir(); }

	void read() { path().read(data); }
	void write() const { path().write(data); }
};

} // mdl

  

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
/*
inline string cut_outer_directory(string path) {
	size_t slash_pos = path.find_first_of("/");
	return path.substr(slash_pos == string::npos ? 0 : slash_pos + 1);
}
*/
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
/*
template<class T>
void shallow_write(T* target) {
	typedef T Source;
	namespace fs = boost::filesystem;
	if (!fs::exists(target->path.dir()))
		fs::create_directories(target->path.dir());
	ofstream out(target->path.path());
	out << *target << endl;
	out.close();
}
*/
struct Path {
	Path() : root(), name(), ext() { }
	Path(const string& n, const string& r, const string& e) : root(r), name(n), ext(e) { }
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
	string path() {
		return (root.size() ? root + "/" : "") + name + (ext.size() ? "." + ext : "");
	}
	string dir() { string p = path(); return p.substr(0, p.find_last_of("/")) + "/"; }
	void name_ext(const string& ne) {
		int i = ne.find_last_of(".");
		name = ne.substr(0, i);
		ext.clear();
		if (i != string::npos) ext = ne.substr(i + 1);
	}
	Path open();
	void read(string& data);
	void write(const string& data);
	Path relative(const string& n) const {
		return Path(n, root, ext);
	}
	string root;
	string name;
	string ext;
};

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

// Template for a deductive system
template<class S, class M, class C>
struct Sys {
	typedef S Source;
	typedef M Math;
	typedef C Config;
	typedef map<string, Timer> Timers;

	Config  config;
	Timers  timers;
	Math    math;
	string  error;

	static const Sys& get() { return mod(); }
	static Sys& mod() { return Lib<Sys>::mod().sys();  }
};

template<typename M, typename T>
inline void initConf(const boost::program_options::variables_map& vm, Config<M, T>& conf) {
	if (vm.count("in"))      conf.in   = vm["in"].as<string>();
	if (vm.count("out"))     conf.out  = vm["out"].as<string>();
	if (vm.count("root"))    conf.root = vm["root"].as<string>();
	if (vm.count("verbose")) conf.verbose = true;
	if (vm.count("deep"))    conf.deep = true;
	if (vm.count("info"))    conf.info = true;
	if (vm.count("help"))    conf.help = true;
}

inline void initOptions(boost::program_options::options_description& desc) {
	namespace po = boost::program_options;
	desc.add_options()
		("help,h",      "print help message")
		("in,i", po::value<string>(),   "input file")
		("out,o", po::value<string>(),  "output file")
		("root,r", po::value<string>(), "root directory (for inclusions)")
		("deep,d",      "deep translation")
		("verbose,v",   "not be silent")
		("info",        "info about math: timings, memory, stats")
	;
}
template<class T>
string show_timer(const char* message, const string& name, const T& timers) {
	return timers.count(name) ? string(message) + show(timers.at(name)) : "";
}

template<class T>
void dump(const T& val) { cout << val; }

template<class T>
struct Table {
	typedef T Type;
	void add(uint n, Type* p = nullptr) {
		if (!refs.count(n)) {
			refs[n].data = p;
		} else {
			Data& d = refs[n];
			if (d.data) throw Error("attempt to reuse live pointer");
			d.data = p;
			for (Type** u : d.users) *u = p;
		}
	}
	void del(uint n) {
		if (!refs.count(n)) throw Error("attempt to delete unknown label");
		Data& d = refs[n];
		if (!d.data) throw Error("attempt to delete null pointer");
		d.data = nullptr;
		for (Type** u : d.users) *u = nullptr;
	}
	void use(uint n, Type*& u) {
		if (!refs.count(n)) throw Error("attempt to use unknown label");
		Data& d = refs[n];
		if (!d.data) throw Error("attempt to use null pointer");
		d.users.insert(&u);
		u = d.data;
	}
	void unuse(uint n, Type*& u) {
		if (!refs.count(n)) throw Error("attempt to unuse unknown label");
		Data& d = refs[n];
		d.users.erase(&u);
	}
	Type* access(uint n) {
		return refs.count(n) ? refs[n].data : nullptr;
	}
	bool has(uint n) const {
		return refs.count(n);
	}

private :
	struct Data {
		Type* data;
		set<Type**> users;
	};
	map<uint, Data> refs;
};


} // mdl

  

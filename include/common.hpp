#pragma once

#include "std.hpp"
#include "location.hpp"
#include "symbol.hpp"
#include "timer.hpp"
#include "actions.hpp"
#include "options.hpp"
#include "lex.hpp"
#include "path.hpp"
#include "conf.hpp"
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

inline ostream& operator << (ostream& os, const Args& args) {
	for (auto& arg : args) os << arg << " ";
	return os;
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


// Library, singleton, which contains a variety of deductive systems
template<typename T>
struct Lib {
	static const Lib& get() { return mod(); }
	static Lib& mod() { static Lib lib; return lib; }

	void init(uint s) {
		contents[s].reset(new T(s));
	}
	template<class TR>
	void init(uint s) {
		contents[s].reset(new TR(s));
	}

	bool has(uint s) const {
		return contents.count(s);
	}

	T& access(uint s) {
		if (!has(s)) init(s);
		return *contents[s];
	}

	template<class TR>
	TR& access(uint s) {
		if (!has(s)) init<TR>(s);
		return static_cast<TR&>(*contents[s]);
	}

private:
	map<uint, unique_ptr<T>> contents;
	Lib() : contents() { }
};

struct Io {
	Io(uint i) :  id(i) { }
	virtual ~Io() { };
	virtual ostream& out() { return cout; }
	virtual ostream& err() { return cerr; }
	struct Std;
	uint id;
};

struct Timers {
	Timers(uint i) : id(i) { }
	Timer& operator[] (const string& s) { return timers[s]; }
	const Timer& operator[] (const string& s) const { return timers.at(s); }
	string show() const;
	map<string, Timer> timers;
	uint id;
};

// Template for a deductive system
template<class S, class M>
struct Sys {
	typedef S System;
	typedef M Math;
	typedef map<string, Action> Actions;

	Sys(uint i) : id(i), timers(i) { }

	const uint id;
	Timers     timers;
	Conf       config;
	Math       math;
	Actions    actions;

	Return exec(const Args& all) {
		if (all.empty()) return Return("no action is chosen", false);
		Args args(all);
		string action = args[0];
		if (!actions.count(action)) return Return("action \"" + action +"\" is unknown", false);
		current() = id;
		args.erase(args.begin());
		timers[action].start();
		Return ret = actions.at(action)(args);
		timers[action].stop();
		return ret;
	}

	Return exec_and_show(const Args& args) {
		bool verbose = conf(id).verbose();
		if (verbose)
			io(id).out() << "doing: " << args << " ... " << flush;
		Return ret = exec(args);
		if (verbose)
			io(id).out() << "done in " << timers[args[0]] << endl;
		if (!ret && ret.text.size())
			io(id).err() << ret.text << endl;
		else if (verbose && ret.text.size())
			io(id).out() << ret.text << endl;
		return ret;
	}

	static const System& get(uint s = -1) { return mod(s); }
	static System& mod(uint s = -1)       { return Lib<System>::mod().access(choose(s));  }
	static Io& io(uint s = -1)            { return Lib<Io>::mod().access(choose(s));  }
	static Timers& timer(uint s = -1)     { return mod(choose(s)).timers;  }
	static Conf& conf(uint s = -1)        { return mod(choose(s)).config;  }

private:
	static uint choose(uint s) { return s == -1 ? current() : s; }
	static set<uint> instances() { static set<uint> inst; return inst; }
	static uint& current() { static uint curr; return curr; }
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
	mutex m;

public:
	void add(uint n, Data* p = nullptr) {
		m.lock();
		if (!p) {
			m.unlock();
			throw Error("adding null pointer, label", Lex::toStr(n));
		}
		if (!refs.count(n)) {
			refs[n].data = p;
		} else {
			Storage& d = refs[n];
			if (d.data) throw Error("reusing live pointer, label", Lex::toStr(n));
			d.data = p;
			for (Data** u : d.users) *u = p;
		}
		m.unlock();
	}
	void del(uint n) {
		m.lock();
		if (!refs.count(n)) {
			m.unlock();
			throw Error("deleting unknown label", Lex::toStr(n));
		}
		Storage& d = refs[n];
		if (!d.data) {
			m.unlock();
			throw Error("deleting null pointer, label", Lex::toStr(n));
		}
		d.data = nullptr;
		for (Data** u : d.users) *u = nullptr;
		m.unlock();
	}
	void use(uint n, Data*& u) {
		m.lock();
		if (!refs.count(n)) {
			m.unlock();
			throw Error("using unknown label", Lex::toStr(n));
		}
		Storage& d = refs[n];
		if (!d.data) {
			m.unlock();
			throw Error("using null pointer, label", Lex::toStr(n));
		}
		d.users.insert(&u);
		u = d.data;
		m.unlock();
	}
	void unuse(uint n, Data*& u) {
		m.lock();
		if (!refs.count(n)) {
			m.unlock();
			throw Error("unusing unknown label", Lex::toStr(n));
		}
		Storage& d = refs[n];
		d.users.erase(&u);
		m.unlock();
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
		static mutex m;
		m.lock();
		for (auto p : refs) delete p.second.data;
		m.unlock();
	}
	int size() const { return refs.size(); }

	typedef typename map<uint, Storage>::iterator iterator;
	typedef typename map<uint, Storage>::const_iterator const_iterator;

	iterator begin() { return refs.begin(); }
	iterator end() { return refs.end(); }

	const_iterator cbegin() const { return refs.cbegin(); }
	const_iterator cend() const { return refs.cend(); }
};

template<class T, class S>
class Owner {
	const uint sys_;
	const uint id_;
public:
	typedef S Sys;
	Owner(uint i) : sys_(Sys::get().id), id_(i) { Sys::mod().math.template get<T>().add(id_, static_cast<T*>(this)); }
	virtual ~Owner() { Sys::mod(sys_).math.template get<T>().del(id_); }
	uint id() const { return id_; }
	uint sys() const { return sys_; }
};

template<class T, class S>
class User {
	T* ptr;
public:
	typedef S Sys;
	User() : ptr(nullptr) { }
	User(uint id) : ptr(nullptr) { use(id); }
	User(const T* p) : ptr(nullptr) { if (p) use(p->id()); }
	User(const User& u) : User(u.id()) { }
	User(User&& u) : User(u.id()) { u.unuse(); }
	~User() { unuse(); }
	void operator = (const T* p) { if (p) use(p->id()); }
	void operator = (const User& u) { use(u.id()); }
	void operator = (User&& u) { use(u.id()); u.unuse(); }

	bool operator == (const User& u) const { return ptr == u.ptr; }
	bool operator != (const User& u) const { return ptr != u.ptr; }
	bool operator < (const User& u) const { return ptr < u.ptr; }
	bool operator <= (const User& u) const { return ptr <= u.ptr; }
	bool operator > (const User& u) const { return ptr > u.ptr; }
	bool operator >= (const User& u) const { return ptr >= u.ptr; }

	bool operator == (const T* p) const { return ptr == p; }
	bool operator != (const T* p) const { return ptr != p; }
	bool operator < (const T* p) const { return ptr < p; }
	bool operator <= (const T* p) const { return ptr <= p; }
	bool operator > (const T* p) const { return ptr > p; }
	bool operator >= (const T* p) const { return ptr >= p; }

	friend bool operator == (const T* p, const User<T, S>& u) { return p == u.ptr; }
	friend bool operator != (const T* p, const User<T, S>& u) { return p != u.ptr; }
	friend bool operator < (const T* p, const User<T, S>& u) { return p < u.ptr; }
	friend bool operator <= (const T* p, const User<T, S>& u) { return p <= u.ptr; }
	friend bool operator > (const T* p, const User<T, S>& u) { return p > u.ptr; }
	friend bool operator >= (const T* p, const User<T, S>& u) { return p >= u.ptr; }

	operator bool() const { return ptr; }

	T* get() { return ptr; }
	const T* get() const { return ptr; }
	uint id() const { return ptr ? ptr->id() : -1; }

	void use(uint id) { unuse(); if (id != -1) Sys::mod().math.template get<T>().use(id, ptr); }
	void unuse() { if (ptr) Sys::mod().math.template get<T>().unuse(ptr->id(), ptr); ptr = nullptr; }
};

template<class Src, class Sys>
struct Source : public Owner<Src, Sys> {
	typedef Owner<Src, Sys> Owner_;
	Source(uint l) : Owner<Src, Sys>(l) { }
	virtual ~Source() { }

	string data;

	Path path() const { return Path(name(), Sys::conf().get("root")); }
	string name() const { return Lex::toStr(Owner_::id()); }
	string dir() const { return path().dir(); }

	void read() { path().read(data); }
	void write() const { path().write(data); }

	// Transitively closed inclusion relation:
	set<Src*> includes;
	set<Src*> included;

	void include(Src* src) {
		includes.insert(src);
		for (Src* s : src->includes) includes.insert(s);
		src->included.insert(dynamic_cast<Src*>(this));
		for (Src* s : src->included) s->included.insert(dynamic_cast<Src*>(this));
	}
};

Return execute(const string& command);

} // mdl

  

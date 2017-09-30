#pragma once

#include "std.hpp"
#include "location.hpp"
#include "symbol.hpp"
#include "timer.hpp"
#include "actions.hpp"
#include "lex.hpp"
#include "io.hpp"
#include "log.hpp"
#include "path.hpp"
#include "conf.hpp"
#include "error.hpp"
#include "xml.hpp"

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
		if (!src->dir().empty() && !fs::exists(src->dir())) {
			if (!fs::create_directories(src->dir()))
				throw Error("failure to create directory", src->dir());
		}
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
		if (!fs::create_directories(dir))
			throw Error("failure to create directory", dir);
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
		contents_[s].reset(new T(s));
	}
	template<class TR>
	void init(uint s) {
		contents_[s].reset(new TR(s));
	}
	void destroy(uint s) {
		contents_[s].reset();
	}

	bool has(uint s) const {
		return contents_.count(s);
	}

	T& access(uint s) {
		if (!has(s)) init(s);
		return *contents_[s];
	}

	template<class TR>
	TR& access(uint s) {
		if (!has(s)) init<TR>(s);
		return static_cast<TR&>(*contents_[s]);
	}

	vector<uint> contents() const {
		vector<uint> ret;
		for (auto& p : contents_) ret.push_back(p.first);
		return ret;
	}

private:
	map<uint, unique_ptr<T>> contents_;
	Lib() : contents_() { }
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
	typedef map<string, Action> Actions;

	Sys(uint i) : id(i) { }
	virtual ~Sys() { }

	static Action help() {
		return Action([](const Args&) {
			for (uint s : Lib<System>::get().contents())
				Io::io().out() << Lex::toStr(s) << " ";
			Io::io().out() << endl;
			return Return();
		}, Descr("show available systems"));
	}
	static Action systems() {
		return Action([](const Args&) {
			Io::io().out() << endl << System::lang() << " actions:" << endl;
			for (auto& a : System::actions())
				Io::io().out() << "\t" << a.first << ": " << a.second.show() << endl;
			return Return();
		}, Descr("show available actions"));
	}
	static Action current() {
		return Action([](const Args& args) {
			curr_() = Lex::toInt(args[0]);
			return Return();
		}, Descr("change current project", Descr::Arg("proj", "name")));
	}
	static Action destroy() {
		return Action([](const Args& args) {
			if (args[0] == "all") {
				for (auto s : Lib<System>::get().contents()) mod(s).math.destroy();
			} else if (args[0].size()) {
				mod(Lex::toInt(args[0])).math.destroy();
			} else {
				mod().math.destroy();
			}
			return Return();
		}, Descr("destroy current project", Descr::Arg("proj", "name", true)));
	}

	const uint id;
	Timers     timers;
	Conf       config;
	Math       math;

	static Return exec(const Args& all) {
		if (all.empty()) return Return("no action is chosen", false);
		Args args(all);
		string action = args[0];
		if (!System::actions().count(action)) return Return("action \"" + action +"\" is unknown", false);
		args.erase(args.begin());
		timer()[action].start();
		Return ret = System::actions().at(action)(args);
		timer()[action].stop();
		Io::io().data() << ret.data;
		return ret;
	}

	static Return exec_and_show(const Args& args) {
		bool verbose = conf().verbose();
		if (verbose)
			Io::io().out() << System::lang() << " doing: " << args << " ... " << flush;
		Return ret = exec(args);
		if (verbose) {
			if (timer()[args[0]].isNegligible())
				Io::io().out() << endl;
			else
				Io::io().out() << "done in " << timer()[args[0]] << endl;
		}
		if (!ret && ret.msg.size())
			Io::io().err() << ret.msg << endl;
		else if (verbose && ret.msg.size())
			Io::io().out() << ret.msg << endl;
		return ret;
	}

	static const System& get(uint s = -1) { return mod(s); }
	static System& mod(uint s = -1)       { return Lib<System>::mod().access(choose(s));  }
	static Timers& timer(uint s = -1)     { return mod(choose(s)).timers;  }
	static Conf& conf(uint s = -1)        { return mod(choose(s)).config;  }
	static uint curr() { return curr_(); }

	static uint make_name(string n) {
		if (!n.size()) return -1;
		boost::trim(n);
		n = n.substr(0, n.find_last_of('.'));
		n = n.substr(n.find(':') + 1);
		return Lex::toInt(n);
	}

	static uint make_sys(string n) {
		boost::trim(n);
		const int i = n.find(':');
		return i == string::npos ? curr() : Lex::toInt(n.substr(0, i));
	}

	static void release() {
		for (auto s : Lib<System>::get().contents()) mod(s).math.destroy();
	}

private:
	static uint choose(uint s) { if (s != -1) return s; else return curr_(); }
	static uint& curr_() { static uint curr; return curr; }
};

template<class T>
string show_timer(const char* message, const string& name, const T& t) {
	return t.timers.count(name) ? string(message) + show(t.timers.at(name)) : "";
}

template<class T>
void dump(const T& val) { cout << val; }

template<class D>
class Table {
	typedef D Data;

	struct Storage {
		Storage() : data(nullptr) { }
		Data* data;
		set<Data**> users;
	};
	map<uint, Storage> refs;
	mutex m;

	void add(uint n, Data* p) {
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
		Storage& d = refs[n];
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

public:
	string show() const {
		ostringstream os;
		os << "size: " << to_string(refs.size()) << endl;
		for (auto& s : refs) {
			os << "\tref: " << Lex::toStr(s.first) << ", users: " << s.second.users.size() << endl;
		}
		return os.str();
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
		refs.clear();
		m.unlock();
	}
	int size() const { return refs.size(); }

	typedef typename map<uint, Storage>::iterator iterator;
	typedef typename map<uint, Storage>::const_iterator const_iterator;

	iterator begin() { return refs.begin(); }
	iterator end() { return refs.end(); }

	const_iterator cbegin() const { return refs.cbegin(); }
	const_iterator cend() const { return refs.cend(); }

	template<class, class> friend class Owner;
	template<class, class> friend class User;
};

inline string xml_sys_id(uint sys, uint id) {
	string ret;
	ret += "sys=\"" + Lex::toStr(sys) + "\" ";
	ret += "id=\"" + Lex::toStr(id) + "\" ";
	ret += "name=\"" + Lex::toStr(id) + "\" ";
	return ret;
}

template<class T, class S>
class Owner : public Tokenable<typename S::Src> {
	const uint sys_;
	const uint id_;
public:
	typedef S Sys;
	typedef typename S::Src Src;
	Owner(uint i, const Token<Src>& t) : Tokenable<Src>(t), sys_(Sys::get().id), id_(i) {
		Sys::mod().math.template get<T>().add(id_, static_cast<T*>(this));
	}
	virtual ~Owner() { Sys::mod(sys_).math.template get<T>().del(id_); }
	uint id() const { return id_; }
	uint sys() const { return sys_; }
	string xml_id() const { return xml_sys_id(sys_, id_); }
};

template<class S>
struct Ref {
	typedef S Sys;
	typedef typename S::Src Src;
	typedef Token<Src> Token_;
	typedef Tokenable<Src> Tokenable_;

	Ref() : count_(0), ptr(nullptr) { }
	void add_ref (const Tokenable_* p) {
		if (count_ && p != ptr) {
			cout << p->token.str() << endl;
			cout << p->token.beg() << endl;
			cout << (int)(p->token.end() - p->token.beg()) << endl;
			cout << p->token.src()->data<< endl;

			string err = "incorrect ref assignment:\n";
			err += "count: " + to_string(count_) + "\n";
			err += "p: " + p->token.show(true) + "\n";
			err += "ptr: " + ptr->token.show(true) + "\n";
			throw Error(err);
		}
		ptr = p;
		++ count_;
	}
	bool del_ref() {
		if (!count_) {
			string err;
			err += "incorrect ref deletion: \n";
			err += "count: " + to_string(count_) + "\n";
			err += "ptr: " + (ptr ? ptr->token.show(true) : "null") + "\n";
			throw Error(err);
		}
		return --count_ == 0;
	}
	const Tokenable_* get() { return ptr; }
	uint count() const { return count_; }
	string str() const { return to_string(count_) + ": " + (ptr ? ptr->token.str() : "<none>"); }
private:
	uint count_;
	const Tokenable_* ptr;

};

template<class S>
class Refs {
	typedef S Sys;
	typedef typename S::Src Src;
	typedef Token<Src> Token_;
	typedef Tokenable<Src> Tokenable_;
	typedef Ref<Sys> Ref_;

public:

	static void add(const Token_& t, const Tokenable_* r) {
		try {
			if (t.is_defined()) refs()[t].add_ref(r);
		} catch (Error& err) {
			err.msg += "token: " + t.show(true) + "\n";
			throw err;
		}
	}
	static void del(const Token_& t) {
		try {
			if (t.is_defined() && refs()[t].del_ref()) refs().erase(t);
		} catch (Error& err) {
			err.msg += "token: " + t.show(true) + "\n";
			throw err;
		}
	}
	static const Tokenable_* find(uint src, const uint line, const uint col) {
		Src* s = Sys::mod().math.template get<Src>().access(src);
		const char* c = locate_position(line, col, s->data.c_str());
		Token_ t(s, c, c);
		return refs().count(t) ? refs().at(t).get() : nullptr;
	}

private:
	Refs() { }
	static map<Token_, Ref_>& refs() {
		static map<Token_, Ref_> r; return r;
	}
};

template<class T, class S>
class User : public Tokenable<typename S::Src> {
	uint sys_;
	uint id_;
	T*   ptr;
public:
	typedef S Sys;
	typedef typename S::Src Src;
	typedef Refs<Sys> Refs_;
	typedef Tokenable<Src> Tokenable_;
	typedef Id<Src> Id_;

	explicit User(uint id = -1, const Token<Src>& t = Token<Src>()) : Tokenable_(t), sys_(-1), id_(-1), ptr(nullptr) { use(id); }
	explicit User(Id_ i) : Tokenable_(i.token), sys_(-1), id_(-1), ptr(nullptr) { use(i.id); }

	User(const T* p, const Token<Src>& t = Token<Src>()) : Tokenable_(t), sys_(-1), id_(-1), ptr(nullptr) { if (p) use(p->id()); }
	User(const User& u) : User(u.id(), u.token) { }
	User(User&& u)      : User(u.id(), u.token) { u.unuse(); }
	~User() { unuse(); }
	void operator = (const T* p)    { use(p->id()); }
	void operator = (const User& u) { Tokenable_::token = u.token; use(u.id()); }
	void operator = (User&& u)      { Tokenable_::token = u.token; use(u.id()); u.unuse(); }

	bool operator == (const User& u) const { return ptr == u.ptr; }
	bool operator != (const User& u) const { return ptr != u.ptr; }
	bool operator < (const User& u) const  { return ptr <  u.ptr; }
	bool operator <= (const User& u) const { return ptr <= u.ptr; }
	bool operator > (const User& u) const  { return ptr >  u.ptr; }
	bool operator >= (const User& u) const { return ptr >= u.ptr; }

	bool operator == (const T* p) const { return ptr == p; }
	bool operator != (const T* p) const { return ptr != p; }
	bool operator < (const T* p) const  { return ptr < p; }
	bool operator <= (const T* p) const { return ptr <= p; }
	bool operator > (const T* p) const  { return ptr > p; }
	bool operator >= (const T* p) const { return ptr >= p; }

	friend bool operator == (const T* p, const User<T, S>& u) { return p == u.ptr; }
	friend bool operator != (const T* p, const User<T, S>& u) { return p != u.ptr; }
	friend bool operator < (const T* p, const User<T, S>& u)  { return p <  u.ptr; }
	friend bool operator <= (const T* p, const User<T, S>& u) { return p <= u.ptr; }
	friend bool operator > (const T* p, const User<T, S>& u)  { return p >  u.ptr; }
	friend bool operator >= (const T* p, const User<T, S>& u) { return p >= u.ptr; }

	operator bool() const { return ptr; }

	T* get() { return ptr; }
	const T* get() const { return ptr; }
	uint id() const { return id_; }
	uint sys() const { return sys_; }
	void set(Id_ i) { Tokenable_::token = i.token; use(i.id); }

	void use(uint id) {
		unuse();
		sys_ = Sys::get().id;
		id_ = id;
		if (id_ != -1) {
			Sys::mod(sys_).math.template get<T>().use(id_, ptr);
			Refs_::add(Tokenable_::token, ptr);
		}
	}
	void unuse() {
		if (id_ != -1) {
			Sys::mod(sys_).math.template get<T>().unuse(id_, ptr);
			Refs_::del(Tokenable_::token);
			id_ = -1;
		}
		ptr = nullptr;
	}
};

template<class Src, class Sys>
struct Source : public Owner<Src, Sys> {
	typedef Owner<Src, Sys> Owner_;
	typedef User<Src, Sys> User_;
	Source(uint l) : Owner<Src, Sys>(l, Token<Src>()) { }
	virtual ~Source() { }

	string data;

	Path path() const { return Path(name(), Sys::conf().get("root"), Sys::ext()); }
	string name() const { return Lex::toStr(Owner_::id()); }
	string dir() const { return path().dir(); }

	void read() { path().read(data); }
	void write() const { path().write(data); }

	// Transitively closed inclusion relation:
	set<User_> includes;
	set<User_> included;

	void include(Src* src) {
		includes.insert(src);
		for (auto& s : src->includes) includes.insert(s);
		src->included.insert(dynamic_cast<Src*>(this));
		for (auto s : src->included) s.get()->included.insert(dynamic_cast<Src*>(this));
		for (auto& s : included) {
			Src* des = const_cast<Src*>(s.get());
			for (auto& d : src->includes) {
				Src* ded = const_cast<Src*>(d.get());
				des->included.insert(ded);
				ded->includes.insert(des);
			}
		}
	}
};

Return execute_command(const string& command);
Return execute(const string& commands);

inline void execute(queue<string>& commands) {
	while (!commands.empty()) {
		string command = commands.front(); commands.pop();
		if (command == "exit" || command == "cancel" || command == "quit") break;
		if (!execute_command(command)) break;
	}
}

} // mdl

  

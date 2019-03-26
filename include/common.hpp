#pragma once

#include "std.hpp"
#include "location.hpp"
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
inline uint find_in_vector(const vector<unique_ptr<T>>& pv, const T* pn) {
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
inline uint find_in_vector(const vector<T*>& pv, const T* pn) {
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
inline vector<T> unite_sorted(const vector<T>& right, const vector<T>& left) {
	vector<T> ret(right.size() + left.size());
	auto end = std::merge(right.begin(), right.end(), left.begin(), left.end(), ret.begin());
	ret.resize(end - ret.begin());
	return ret;
}

template<class T>
inline bool sets_intersect(const set<T>& right, const set<T>& left) {
	for (const T& t : right) {
		if (left.count(t)) {
			return true;
		}
	}
	return false;
}

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
void dump(const T& val) { cout << val; }

template<class D>
inline string shower(const D&) { return ""; }

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

struct Writable {
	virtual ~Writable() { }
	virtual void write(ostream&, const Indent& = Indent()) const = 0;
	string show() const {
		ostringstream oss; write(oss); return oss.str();
	}
};

struct Referable {
	virtual ~Referable() { }
	virtual void ref(ostream& os) const = 0;
};

inline ostream& operator << (ostream& os, const Writable& w) {
	w.write(os); return os;
}

//inline string show(const Writable& w) {
//	ostringstream ss; w.write(ss); return ss.str();
//}

inline void dump(const Writable& w) {
	w.write(cout);
}

template<class Sys>
void write(uint src, bool deep) {
	typedef typename Sys::Src Source;
	if (deep) {
		vector<const Source*> sources;
		for (const auto& p : Sys::get().math.template get<Source>()) {
			const Source* s = p.second.data;
			s->ensure_dir_exists();
			sources.push_back(s);
		}
		tbb::parallel_for (tbb::blocked_range<size_t>(0, sources.size()),
			[sources] (const tbb::blocked_range<size_t>& r) {
				for (size_t i = r.begin(); i != r.end(); ++i)
					sources[i]->write_self();
			}
		);
	} else {
		if (const Source* s = Sys::get().math.template get<Source>().access(src)) {
			s->write_self();
		} else {
			throw Error("unknown source", Lex::toStr(src));
		}
	}
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
			Io::io().out() << endl << System::lang() << " actions:" << endl;
			for (auto& a : System::actions()) {
				Io::io().out() << "\t" << a.first << ": " << a.second.show() << endl;
			}
			return Return();
		}, Descr("show available actions"));
	}
	static Action systems() {
		return Action([](const Args&) {
			for (uint s : Lib<System>::get().contents()) {
				Io::io().out() << Lex::toStr(s) << ":" << endl;
				Io::io().out() << get(s).config.show() << endl;
			}
			Io::io().out() << endl;
			return Return();
		}, Descr("show available systems"));
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
		if (all.empty()) {
			return Return("no action is chosen", false);
		}
		Args args(all);
		string action = args[0];
		if (!System::actions().count(action)) {
			return Return("action \"" + action +"\" is unknown", false);
		}
		args.erase(args.begin());
		timer()[action].start();
		Return ret = System::actions().at(action)(args);
		timer()[action].stop();
		Io::io().data() << ret.data;
		return ret;
	}

	static Return exec_and_show(const Args& args) {
		bool verbose = conf().verbose();
		if (verbose) {
			Io::io().out() << System::lang() << " doing: " << args << " ... " << flush;
		}
		Return ret = exec(args);
		if (verbose && !args.empty()) {
			if (timer()[args[0]].isNegligible()) {
				Io::io().out() << "done.";
			} else {
				Io::io().out() << "done in " << timer()[args[0]] << ". ";
			}
			Io::io().out() << endl;
			if (!ret.success()) {
				Io::io().out() << "Failed";
				if (ret.code != -1) {
					Io::io().out() << ", code: " << ret.code;
				}
				Io::io().out() << endl;
			}
		}
		if (!ret && ret.msg.size()) {
			Io::io().err() << ret.msg << endl;
		} else if (verbose && ret.msg.size()) {
			Io::io().out() << ret.msg << endl;
		}
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
		for (auto s : Lib<System>::get().contents()) {
			mod(s).math.destroy();
		}
	}

private:
	static uint choose(uint s) { if (s != -1) return s; else return curr_(); }
	static uint& curr_() { static uint curr = Lex::toInt("default_project"); return curr; }
};

template<class T>
string show_timer(const char* message, const string& name, const T& t) {
	return t.timers.count(name) ? string(message) + show(t.timers.at(name)) : "";
}

template<class D>
class Table {
	typedef D Data;

	struct Storage {
		Storage() : data(nullptr) { }
		Data* data;
		set<Data**> users;
	};
	typedef cmap<uint, Storage> Refs;
	Refs refs;
	bool strict;

	void add(uint n, Data* p) {
		if (!p) {
			throw Error("adding null pointer, label", Lex::toStr(n));
		}
		typename Refs::accessor a;
		if (refs.insert(a, n)) {
			a->second.data = p;
		} else {
			if (a->second.data) {
				if (strict) throw Error("reusing live pointer, label", Lex::toStr(n));
			} else {
				a->second.data = p;
				for (Data** u : a->second.users) *u = p;
			}
		}
	}
	void del(uint n) {
		typename Refs::accessor a;
		if (refs.find(a, n)) {
			if (!a->second.data) {
				if (strict) throw Error("deleting null pointer, label", Lex::toStr(n));
			} else {
				a->second.data = nullptr;
				for (Data** u : a->second.users) *u = nullptr;
			}
		} else {
			throw Error("deleting unknown label", Lex::toStr(n));
		}
	}
	void use(uint n, Data*& u) {
		typename Refs::accessor a;
		refs.insert(a, n);
		a->second.users.insert(&u);
		u = a->second.data;
	}
	void unuse(uint n, Data*& u) {
		typename Refs::accessor a;
		if (refs.find(a, n)) {
			a->second.users.erase(&u);
		} else {
			throw Error("unusing unknown label", Lex::toStr(n));
		}
	}

public:
	Table(bool s = true) : strict(s) { }

	string show_table() const {
		ostringstream os;
		os << "size: " << to_string(refs.size()) << endl;
		for (auto& s : refs) {
			os << "\tref: " << Lex::toStr(s.first) << ", users: " << s.second.users.size() << endl;
		}
		return os.str();
	}
	Data* access(uint n) {
		typename Refs::accessor a;
		return refs.find(a, n) ? a->second.data : nullptr;
	}
	const Data* access(uint n) const {
		typename Refs::accessor a;
		return refs.find(a, n) ? a->second.data : nullptr;
	}
	bool has(uint n) const {
		typename Refs::const_accessor a;
		return refs.find(a, n) && a->second.data;
	}
	void destroy() {
		static mutex m;
		m.lock();
		for (auto p : refs) delete p.second.data;
		refs.clear();
		m.unlock();
	}
	int size() const { return refs.size(); }

	typedef typename Refs::iterator iterator;
	typedef typename Refs::const_iterator const_iterator;

	iterator begin() { return refs.begin(); }
	iterator end() { return refs.end(); }

	const_iterator begin() const { return refs.begin(); }
	const_iterator end() const { return refs.end(); }

	template<class, class> friend class Owner;
	template<class, class> friend class User;

	void rehash() { refs.rehash(); }
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
	virtual ~Owner() {
		Sys::mod(sys_).math.template get<T>().del(id_);
	}
	uint id() const { return id_; }
	uint sys() const { return sys_; }
	string xml_id() const { return xml_sys_id(sys_, id_); }
};

template<class T, class S>
class User : public Id<typename S::Src, true> {
	uint sys_;
	T*   ptr;
public:
	typedef S Sys;
	typedef typename S::Src Src;
	typedef Tokenable<Src> Tokenable_;
	typedef Id<Src, true> Id_;

	explicit User(uint id = -1, const Token<Src>& t = Token<Src>()) : Id_(-1, t), sys_(-1), ptr(nullptr) { use(id); }
	explicit User(Id_ i) : Id_(-1, i.token), sys_(-1), ptr(nullptr) { use(i.id); }

	User(const T* p, const Token<Src>& t = Token<Src>()) : Id_(-1, t), sys_(-1), ptr(nullptr) { if (p) use(p->id()); }
	User(const User& u) : User(u.id(), u.token) { }
	User(User&& u)      : User(u.id(), u.token) { u.unuse(); }
	virtual ~User() { unuse(); }
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

	T* operator -> () { return ptr; }
	const T* operator -> () const { return ptr; }
	T& operator * () { return *ptr; }
	const T& operator * () const { return *ptr; }

	friend bool operator == (const T* p, const User<T, S>& u) { return p == u.ptr; }
	friend bool operator != (const T* p, const User<T, S>& u) { return p != u.ptr; }
	friend bool operator < (const T* p, const User<T, S>& u)  { return p <  u.ptr; }
	friend bool operator <= (const T* p, const User<T, S>& u) { return p <= u.ptr; }
	friend bool operator > (const T* p, const User<T, S>& u)  { return p >  u.ptr; }
	friend bool operator >= (const T* p, const User<T, S>& u) { return p >= u.ptr; }

	operator bool() const { return ptr; }

	T* get() { if (!ptr) throw Error("unknown id", Lex::toStr(id())); return ptr; }
	const T* get() const { if (!ptr) throw Error("unknown id", Lex::toStr(id())); return ptr; }
	uint id() const { return Id_::id; }
	uint sys() const { return sys_; }
	void set(Id_ i) { Tokenable_::token = i.token; use(i.id); }
	const Tokenable_* ref() const override { return ptr; }

	void use(uint id) {
		unuse();
		sys_ = Sys::get().id;
		Id_::id = id;
		if (Id_::id != -1) {
			Sys::mod(sys_).math.template get<T>().use(Id_::id, ptr);
		}
	}
	void unuse() {
		if (Id_::id != -1) {
			Sys::mod(sys_).math.template get<T>().unuse(Id_::id, ptr);
			Id_::id = -1;
		}
		ptr = nullptr;
	}
};

template<class T, class S>
class IndirectUser : public Id<typename S::Src, false> {
	T* ptr;
public:
	typedef S Sys;
	typedef typename S::Src Src;
	typedef Id<Src, false> Id_;

	explicit IndirectUser(uint id = -1) : Id_(-1), ptr(nullptr) { use(id); }
	explicit IndirectUser(Id_ i) : Id_(-1, i.token), ptr(nullptr) { use(i.id); }
	IndirectUser(const IndirectUser& u) = delete;
	~IndirectUser() { if (ptr) throw Error("deleting live id (in IndirectUser)", Lex::toStr(id())); }

	void operator = (const T* p)    { use(p->id(), p->sys()); }
	void operator = (const IndirectUser& u) = delete;

	bool operator == (const IndirectUser& u) const { return ptr == u.ptr; }
	bool operator != (const IndirectUser& u) const { return ptr != u.ptr; }
	bool operator < (const IndirectUser& u) const  { return ptr <  u.ptr; }
	bool operator <= (const IndirectUser& u) const { return ptr <= u.ptr; }
	bool operator > (const IndirectUser& u) const  { return ptr >  u.ptr; }
	bool operator >= (const IndirectUser& u) const { return ptr >= u.ptr; }

	bool operator == (const T* p) const { return ptr == p; }
	bool operator != (const T* p) const { return ptr != p; }
	bool operator < (const T* p) const  { return ptr < p; }
	bool operator <= (const T* p) const { return ptr <= p; }
	bool operator > (const T* p) const  { return ptr > p; }
	bool operator >= (const T* p) const { return ptr >= p; }

	T* operator -> () { return ptr; }
	const T* operator -> () const { return ptr; }
	T& operator * () { return *ptr; }
	const T& operator * () const { return *ptr; }

	friend bool operator == (const T* p, const IndirectUser<T, S>& u) { return p == u.ptr; }
	friend bool operator != (const T* p, const IndirectUser<T, S>& u) { return p != u.ptr; }
	friend bool operator < (const T* p, const IndirectUser<T, S>& u)  { return p <  u.ptr; }
	friend bool operator <= (const T* p, const IndirectUser<T, S>& u) { return p <= u.ptr; }
	friend bool operator > (const T* p, const IndirectUser<T, S>& u)  { return p >  u.ptr; }
	friend bool operator >= (const T* p, const IndirectUser<T, S>& u) { return p >= u.ptr; }

	operator bool() const { return ptr; }

	T* get() { if (!ptr) throw Error("unknown id", Lex::toStr(id())); return ptr; }
	const T* get() const { if (!ptr) throw Error("unknown id", Lex::toStr(id())); return ptr; }
	uint id() const { return Id_::id; }

	void use(uint id, uint sys) {
		unuse(sys);
		Id_::id = id;
		if (Id_::id != -1) {
			Sys::mod(sys).math.template get<T>().use(Id_::id, ptr);
		}
	}
	void unuse(uint sys) {
		if (Id_::id != -1) {
			Sys::mod(sys).math.template get<T>().unuse(Id_::id, ptr);
			Id_::id = -1;
		}
		ptr = nullptr;
	}
};


template<class Src, class Sys>
struct Source : public Owner<Src, Sys>, public Writable {
	typedef Owner<Src, Sys> Owner_;
	typedef User<Src, Sys> User_;
	typedef set<User_>     SrcSet;

	enum class Closure { UNKNOWN, IN_PROGRESS, DONE, };

	Source(uint l) : Owner<Src, Sys>(l, Token<Src>()), parsed(false), closureState(Closure::UNKNOWN) { }
	virtual ~Source() { }

	const string& data() { return data_; }
	const string& data() const { return data_; }

	Path path() const { return Path(name(), Sys::conf().get("root"), Sys::ext()); }
	string name() const { return Lex::toStr(Owner_::id()); }
	string dir() const { return path().dir(); }

	void read(const vector<Patch>* patches = nullptr) {
		path().read(data_, patches);
		timestamp_ = efs::last_write_time(path().path());
		parsed = false;
	}

	// Transitively closed inclusion relation:
	bool includes(const Src* s) const {
		return all_includes.find(User_(s)) != all_includes.end();
	}
	void include(Src* src) {
		if (src->id() == Owner_::id()) {
			throw Error("source cannot include itself", Lex::toStr(src->id()));
		}
		this_includes.emplace(src->id());
		all_includes.emplace(src->id());
	}
	string showInclusionInfo() const {
		string str;
		str += string("Source: ") + Lex::toStr(Owner_::id()) + "\n";
		str += "this_includes:\n";
		for (auto s : this_includes) str += "\t" + Lex::toStr(s) + "\n";
		str += "all_includes:\n";
		for (auto s : all_includes) str += "\t" + Lex::toStr(s) + "\n";
		return str;
	}

	bool parsed;

	void transitive_closure() {
		switch (closureState) {
		case Closure::DONE: return;
		case Closure::IN_PROGRESS: throw Error("Cyclic source dependency", Lex::toStr(Owner_::id()));
		case Closure::UNKNOWN:
			closureState = Closure::IN_PROGRESS;
			for (const auto& s : this_includes) {
				const_cast<Src*>(s.get())->transitive_closure();
				for (const auto& inc : s.get()->all_includes) {
					all_includes.emplace(inc.id());
				}
			}
			closureState = Closure::DONE;
		}
	}

	bool has_changed() const {
		return !boost::filesystem::exists(path().path()) || timestamp_ != efs::last_write_time(path().path());
	}

	void ensure_dir_exists() const {
		namespace fs = boost::filesystem;
		if (dir().empty() || !fs::exists(dir())) {
			if (!fs::create_directories(dir())) {
				throw Error("failure to create directory", dir());
			}
		}
	}

	void write_self() const {
		ofstream out(path().path());
		write(out);
	}

private:
	template<class, class> friend struct Source;

	Closure closureState;
	SrcSet  this_includes;
	SrcSet  all_includes;
	string  data_;
	efs::file_time_type timestamp_;
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

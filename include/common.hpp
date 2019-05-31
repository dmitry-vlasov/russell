#pragma once

#include <numeric>
#include <cmath>

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
#include "lib.hpp"

namespace mdl {

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
	return t.timers.count(name) ? string(message) + t.timers.at(name).show() : "";
}

template<class D>
class Table {
	typedef D Data;

	struct Storage {
		Storage() : data(nullptr) { }
		Data* data;
		hset<Data**> users;
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
class Owner : public Id<S>, public WithToken<typename S::Src> {
public:
	typedef S Sys;
	typedef typename S::Src Src;
	typedef Id<S> Id_;
	typedef WithToken<Src> WithToken_;

	Owner(uint i, const Token<Src>& t) : Id_(i), WithToken_(t) {
		Sys::mod().math.template get<T>().add(Id_::id(), static_cast<T*>(this));
	}
	~Owner() {
		Sys::mod(Id_::sys()).math.template get<T>().del(Id_::id());
	}
	string xml_id() const { return xml_sys_id(Id_::sys(), Id_::id()); }
};

template<class T, class S>
class User : public Id<S> {
protected:
	T* ptr;
public:
	typedef S Sys;
	typedef typename S::Src Src;
	typedef Id<S> Id_;

	explicit User(uint id = -1) : ptr(nullptr) { use(id); }
	explicit User(Id_ i) : ptr(nullptr) { use(i.id(), i.sys()); }
	explicit User(const T* p) : ptr(nullptr) { if (p) use(p->id(), p->sys()); }
	User(const User& u) :User(u.id()) { }
	User(User&& u) :User(u.id()) { u.unuse(); }
	~User() { unuse(); }

	void operator = (const T* p) { if (p) use(p->id(), p->sys()); }
	void operator = (const User& u) { use(u.id(), u.sys()); }

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

	T* get() {
		if (!ptr) {
			throw Error("unknown id", Lex::toStr(Id_::id()));
		}
		return ptr;
	}
	const T* get() const {
		if (!ptr) {
			throw Error("unknown id", Lex::toStr(Id_::id()));
		}
		return ptr;
	}

	void set(const T* p) { use(p->id(), p->sys()); }
	void set(uint id) { use(id); }
	void set(Id_ id) { use(id.id(), id.sys()); }

	bool is_undef() const { return Id_::id() == -1; }

	void use(uint id, uint s = -1) {
		unuse();
		Id_::set(id, (s == -1) ? Sys::get().id : s);
		if (Id_::id() != -1) {
			Sys::mod(Id_::sys()).math.template get<T>().use(Id_::id(), ptr);
		}
	}
	void unuse() {
		if (Id_::id() != -1) {
			Sys::mod(Id_::sys()).math.template get<T>().unuse(Id_::id(), ptr);
			Id_::drop();
		}
		ptr = nullptr;
	}
};

template<class Src, class Sys>
struct Source : public Writable, public Owner<Src, Sys> {
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
		for (auto& s : this_includes) {
			str += "\t" + Lex::toStr(s->id()) + "\n";
		}
		str += "all_includes:\n";
		for (auto& s : all_includes) {
			str += "\t" + Lex::toStr(s->id()) + "\n";
		}
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

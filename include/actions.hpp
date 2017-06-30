#pragma once

#include "lex.hpp"
#include "error.hpp"

namespace mdl {

struct Return {
	Return(const string& m = "", bool s = true) : msg(m), code(s ? 0 : -1) { }
	Return(const string& m, const string& d, bool s = true) : msg(m), data(d), code(s ? 0 : -1) { }
	operator bool() const { return success(); }
	string msg;
	string data;
	uint   code;

	bool success() const { return !code; }

	string to_string() const;
	static Return from_string(const string&);
};

typedef vector<string> Args;
typedef function<Return (const Args&)> Function;

inline Function wrap_action(Function f, int arity) {
	return [f, arity](const Args& args) {
		if (arity > 0 && args.size() < arity)
			return Return("wrong number of arguments, should be not less then " + to_string(arity), false);
		try {
			return f(args);
		} catch (const Error& err) {
			return Return(string("failure: ") + err.what(), false);
		} catch (std::exception& ex) {
			return Return(string("failure: ") + ex.what(), false);
		} catch (...) {
			return Return("failure", false);
		}
	};
}

struct Descr {
	struct Arg {
		Arg() : opt(false) { }
		Arg(const string& n, const string& v, bool o = false, const string& d = "") : name(n), value(v), opt(o), def(d) { }
		string name;
		string value;
		bool   opt;
		string def;
		string show() const { return name + (value.size() ? "=<" + value + ">" : ""); }
		bool fits(const string& arg) const {
			return (arg.substr(0, arg.find_last_of("=")) == name);
		}
		bool parse(const string& arg, string& value) const {
			int i = arg.find_last_of("=");
			if (arg.substr(0, i) != name) return false;
			value = (i == string::npos) ? "" : arg.substr(i + 1);
			return true;
		}
	};
	Descr() : arity(0), keep_args(false) { }
	Descr(const string& d) : descr(d), arity(0), keep_args(false) { }
	Descr(const string& d, const Arg& a1, bool k = false) : descr(d), arity(0), keep_args(k) {
		args.push_back(a1);
		calculate_arity();
	}
	Descr(const string& d, const Arg& a1, const Arg& a2, bool k = false) : descr(d), arity(0), keep_args(k) {
		args.push_back(a1);
		args.push_back(a2);
		calculate_arity();
	}
	Descr(const string& d, const Arg& a1, const Arg& a2, const Arg& a3, bool k = false) : descr(d), arity(3), keep_args(k) {
		args.push_back(a1);
		args.push_back(a2);
		args.push_back(a3);
		calculate_arity();
	}
	Descr(const string& d, int a, bool k = false) : descr(d), arity(a), keep_args(k) { }

	string      descr;
	int         arity;
	vector<Arg> args;
	bool        keep_args;

	string show() const {
		string s;
		for (const Arg& arg : args) if (!arg.opt) s += arg.show() + " ";
		if (has_optional()) {
			s += "optional: ";
			for (const Arg& arg : args) if (arg.opt) s += arg.show() + " ";
		}
		if (descr.size()) s += " - " + descr;
		return s;
	}

	Args prepare(const Args& args_orig) const {
		if (keep_args) return args_orig;
		Args args_reord;
		for (auto& arg: args) {
			string value;
			if (!arg.opt && find_arg(arg, value, args_orig))
				args_reord.push_back(value);
		}
		for (auto& arg: args) {
			string value;
			if (arg.opt) {
				if (find_arg(arg, value, args_orig))
					args_reord.push_back(value);
				else
					args_reord.push_back(arg.def);
			}
		}
		return args_reord;
	}

private:
	bool find_arg(const Arg& arg, string& value, const Args& args_orig) const {
		for (auto& s : args_orig) {
			if (arg.parse(s, value)) return true;
		}
		if (!arg.opt) throw Error("mandatory argument is missed", arg.show());
		return false;
	}
	void calculate_arity() {
		arity = 0;
		for (const Arg& a : args) if (!a.opt) ++ arity;
	}
	bool has_optional() const {
		for (const Arg& a : args) if (a.opt) return true; return false;
	}
};

class Action {
public:
	Action() { }
	Action(Function a, const Descr& d) : action(wrap_action(a, d.arity)), descr(d) { }
	Return operator() (const Args& args) const { return action(descr.prepare(args)); }
	string show() const { return descr.show(); }

private:
	Function action;
	Descr    descr;
};


} // mdl

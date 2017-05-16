#pragma once

#include "lex.hpp"
#include "error.hpp"

namespace mdl {

struct Return {
	Return(const string& t = "", bool s = true, any d = any()) : text(t), data(d), success(s) { }
	operator bool() const { return success; }
	string text;
	any    data;
	bool   success;

	string to_string() const {
		return (success ? string("0") : string("1")) + text;
	}
	static Return from_string(const string& s) {
		return Return(s.substr(1), s[0] == '0');
	}
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

class Action {
public:
	Action() : arity(0) { }
	Action(Function a, int n, const string& d = "") : action(wrap_action(a, n)), arity(n), descr(d) { }
	Return operator() (const Args& args) const { return action(args); }
	const string& show() const { return descr; }

private:
	Function action;
	int      arity;
	string   descr;
};


} // mdl

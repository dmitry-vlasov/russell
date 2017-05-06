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
			return Return("failure", false, err.what());
		} catch (std::exception& ex) {
			return Return("failure", false, ex.what());
		} catch (...) {
			return Return("failure", false);
		}
	};
}

} // mdl

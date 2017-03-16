#pragma once

#include "lex.hpp"
#include "error.hpp"

namespace mdl {

struct Return {
	Return(const string& t = "", bool s = true, any d = any()) : text(t), data(d), success(s) { }
	string text;
	any    data;
	bool   success;
};

typedef vector<string> Args;
typedef function<Return (const Args&)> Action;

typedef void (*ZeroAryProc)();
typedef void (*UnAryProc)(uint);
typedef void (*BinAryProc)(uint, uint);

typedef string (*ZeroAryFunc)();
typedef string (*UnAryFunc)(uint);
typedef string (*BinAryFunc)(uint, uint);

inline Action zeroary_proc(ZeroAryProc f) {
	return [f](const Args& args) {
		try {
			f();
			return Return("success");
		} catch (const Error& err) {
			return Return("failure", false, err.what());
		} catch (std::exception& ex) {
			return Return("failure", false, ex.what());
		} catch (...) {
			return Return("failure", false);
		}
	};
}

inline Action unary_proc(UnAryProc f) {
	return [f](const Args& args) {
		if (args.size() < 1)
			return Return("failure: not enough arguments", false);
		try {
			f(Lex::toInt(args[0]));
			return Return("success");
		} catch (const Error& err) {
			return Return("failure", false, err.what());
		} catch (std::exception& ex) {
			return Return("failure", false, ex.what());
		} catch (...) {
			return Return("failure", false);
		}
	};
}

inline Action binary_proc(BinAryProc f) {
	return [f](const Args& args) {
		if (args.size() < 2)
			return Return("failure: not enough arguments", false);
		try {
			f(Lex::toInt(args[0]), Lex::toInt(args[1]));
			return Return("success");
		} catch (const Error& err) {
			return Return("failure", false, err.what());
		} catch (std::exception& ex) {
			return Return("failure", false, ex.what());
		} catch (...) {
			return Return("failure", false);
		}
	};
}

inline Action zeroary_func(ZeroAryFunc f) {
	return [f](const Args& args) {
		try {
			string ret = f();
			return Return("success", true, ret);
		} catch (const Error& err) {
			return Return("failure", false, err.what());
		} catch (std::exception& ex) {
			return Return("failure", false, ex.what());
		} catch (...) {
			return Return("failure", false);
		}
	};
}

inline Action unary_func(UnAryFunc f) {
	return [f](const Args& args) {
		if (args.size() < 1)
			return Return("failure: not enough arguments", false);
		try {
			string ret = f(Lex::toInt(args[0]));
			return Return("success", true, ret);
		} catch (const Error& err) {
			return Return("failure", false, err.what());
		} catch (std::exception& ex) {
			return Return("failure", false, ex.what());
		} catch (...) {
			return Return("failure", false);
		}
	};
}

inline Action binary_func(BinAryFunc f) {
	return [f](const Args& args) {
		if (args.size() < 2)
			return Return("failure: not enough arguments", false);
		try {
			string ret = f(Lex::toInt(args[0]), Lex::toInt(args[1]));
			return Return("success", true, ret);
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

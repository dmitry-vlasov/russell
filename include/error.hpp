#pragma once

#include "std.hpp"
#include "location.hpp"
#include "lex.hpp"

namespace mdl {

class Error : public std::exception {
public :
	virtual ~Error() { }

	void location(const Location& loc) {
		msg += "\nat: " + show(loc);
	}
	template<class T>
	void location(const T& token) {
		msg += "\nat: " + token.show();
	}
	Error (const string& str, const Location* loc = nullptr) throw() :
	msg() {
		msg += "error: " + str;
		if (loc) location(*loc);
		msg += "\n";
	}
	template<class T>
	Error (const string& str, const T& token) throw() :
	msg() {
		msg += "error: " + str;
		msg += "\nat: " + token.show();
		msg += "\n";
	}
	Error (const string& str, const string& s, const Location* loc = nullptr) throw() :
	msg() {
		msg += "error: " + str + " : " + s;
		if (loc) location(*loc);
		msg += "\n";
	}
	template<class T>
	Error (const string& str, const string& s, const T& token) throw() :
	msg() {
		msg += "error: " + str + " : " + s;
		msg += "\nat: " + token.show();
		msg += "\n";
	}
	virtual const char* what() const throw() {
		return msg.c_str();
	}
	string   msg;
};

} // mdl

  

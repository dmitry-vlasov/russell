#pragma once

#include <boost/program_options.hpp>

#include "std.hpp"
#include "location.hpp"
#include "symbol.hpp"
#include "timer.hpp"
#include "actions.hpp"
#include "lex.hpp"

namespace mdl {

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

} // mdl

  

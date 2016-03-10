#pragma once

#include <exception>
#include "std.hpp"

namespace mdl {
  
class Location;

class Error : public std::exception {
public :
	Error (const char* str, const Location* loc = nullptr) throw() :
	msg() {
		msg += "error: ";
		msg += str;
		if (loc) {
			msg += "\nat: ";
			msg += show(*loc);
		}
	}
	Error (const char* str, const string& s, const Location* loc = nullptr) throw() :
	msg() {
		msg += "error: ";
		msg += str;
		msg += " : ";
		msg += s;
		if (loc) {
			msg += "\nat: ";
			msg += show(*loc);
		}
	}
	virtual const char* what() const throw() {
		return msg.c_str();
	}
	string msg;
};
  
}

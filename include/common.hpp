#pragma once

#include "std.hpp"
#include "location.hpp"
#include "error.hpp"
#include "table.hpp"
#include "timer.hpp"
#include "expr.hpp"

#define VERSION "0.2"

namespace mdl {

class indent {
	int  num;
	char del;
public:
	indent(int n = 1, char d = '\t') : num(n), del(d) {
	}
	void make(ostream& os) {
		while (num --) os << del;
	}
};

inline ostream& operator <<(ostream& os, indent ind) {
	ind.make(os);
	return os;
}

}

  

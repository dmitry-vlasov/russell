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
	void write(ostream& os) {
		while (num --) os << del;
	}
};

class label {
	uint lab;
public:
	label(uint l) : lab(l) {
	}
	void write(ostream& os);
};

inline ostream& operator << (ostream& os, indent ind) {
	ind.write(os);
	return os;
}

inline ostream& operator << (ostream& os, label lab) {
	lab.write(os);
	return os;
}

}

  

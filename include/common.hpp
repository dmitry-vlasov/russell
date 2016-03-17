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
	static string paragraph(const string& str, string d = "\t") {
		string indented;
		for (char ch : str) {
			if (ch == '\n') indented += "\n" + d;
			else            indented += ch;
		}
		return indented;
	}
};

class label {
	uint lab;
public:
	label(uint l) : lab(l) {
	}
	void write(ostream& os);
	string show();
};

class symbol {
	uint lit;
public:
	symbol(uint l) : lit(l) {
	}
	void write(ostream& os);
	string show();
};

inline ostream& operator << (ostream& os, indent ind) {
	ind.write(os);
	return os;
}

inline ostream& operator << (ostream& os, label lab) {
	lab.write(os);
	return os;
}

template<int len_f = 64, int len_b = 8>
struct wrapper {
	wrapper(string::const_iterator it) :
	str (it - len_b, it + len_f){ }
	string str;
};

template<int len_f, int len_b>
std::ostream& operator << (std::ostream& os, const wrapper<len_f, len_b>& wr){
	os << wr.str;
	return os;
}

}

  

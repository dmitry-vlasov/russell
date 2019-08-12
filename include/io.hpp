#pragma once

#include "std.hpp"

namespace mdl {

struct Io {
	enum Kind { STD, STR };

	ostream& out()  { return kind == STD ? cout : out_; }
	ostream& err()  { return kind == STD ? cerr : err_; }
	ostream& data() { return data_; }

	void println(const string& msg, bool e = false) {
		static mutex m;
		m.lock();
		if (e) {
			err() << msg << endl;
		} else {
			out() << msg << endl;
		}
		m.unlock();
	}

	Kind kind = STD;

	static Io& io() { static Io io; return io;  }

private:
	stringstream out_;
	stringstream err_;
	stringstream data_;
};

} // mdl


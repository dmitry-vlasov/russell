#pragma once

#include "std.hpp"

namespace mdl {

struct Io {
	enum Kind { STD, STR };

	ostream& out()  { return kind == STD ? cout : out_; }
	ostream& err()  { return kind == STD ? cerr : err_; }
	ostream& data() { return data_; }

	Kind kind = STD;

	static Io& io() { static Io io; return io;  }

private:
	stringstream out_;
	stringstream err_;
	stringstream data_;
};

} // mdl


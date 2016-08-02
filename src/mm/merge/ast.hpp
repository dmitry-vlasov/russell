#pragma once

#include "common.hpp"

namespace mdl { namespace mm { namespace merge {

struct Source {
	//Source(string r, string n) : contents(), root(r), name(n) { }
	static Source& mod() { static Source src; return src; }
	static const Source& get() { return mod(); }
	stringstream contents;
	//string root;
	//string name;
};

void parse(string path);

}}} // mdl::mm::merge



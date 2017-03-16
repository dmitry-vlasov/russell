#pragma once

#include "common.hpp"

namespace mdl { namespace mm { namespace merge {

struct Source {
	static Source& mod() { static Source src; return src; }
	static const Source& get() { return mod(); }
	stringstream contents;
};

void parse(const Path& path);

}}} // mdl::mm::merge



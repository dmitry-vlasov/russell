#pragma once

#include "common.hpp"

namespace mdl { namespace mm { namespace merge {

struct Merger {
	void read(Path in);
	void merge();
	void save(Path out);

	ostringstream source;
};

//void parse(string path);

}}} // mdl::mm::merge



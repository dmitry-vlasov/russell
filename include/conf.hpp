#pragma once

#include "std.hpp"
#include "path.hpp"

namespace mdl {

enum class Lang { NONE, MM, SMM, RUS, DEFAULT = NONE };

// Configuration for a deductive system
struct Conf {
	typedef map<string, string> Opts;

	Conf() :
	verbose(false), deep(false),
	in(), out(), target(Lang::DEFAULT) { }

	bool verbose;
	bool deep;

	Path in;
	Path out;

	string mode;
	Lang   target;

	Opts opts;
};

}

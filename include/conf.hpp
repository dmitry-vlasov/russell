#pragma once

#include "std.hpp"
#include "path.hpp"

namespace mdl {

enum class Lang { NONE, MM, SMM, RUS, DEFAULT = NONE };
enum class Mode { NONE, TRANSL, CUT, MERGE, PROVE, DEFAULT = NONE };

// Configuration for a deductive system
struct Conf {
	Conf() :
	verbose(false), info(false), deep(false),
	in(), out(),
	mode(Mode::DEFAULT), target(Lang::DEFAULT) { }

	bool verbose;
	bool info;
	bool deep;

	Path in;
	Path out;

	Mode mode;
	Lang target;
};

}

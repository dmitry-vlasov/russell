#pragma once

#include "rus_prover_expr.hpp"

namespace mdl { namespace rus { namespace prover {

struct Unified {
	Unified(bool ok = false) : sub(ok) { }
	Subst sub;
	LightTree term;
};

Unified unify(const vector<const LightTree*>& ex);

}}}


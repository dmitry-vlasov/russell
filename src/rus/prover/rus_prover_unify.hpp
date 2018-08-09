#pragma once

#include "rus_prover_expr.hpp"

namespace mdl { namespace rus { namespace prover {

struct Unified {
	Unified(bool ok = false) : sub(ok), term(nullptr) { }
	Subst sub;
	unique_ptr<LightTree> term;
};

Unified unify(const vector<const LightTree*>& ex);

}}}


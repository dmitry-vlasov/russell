#pragma once

#include "rus_prover_expr.hpp"

namespace mdl { namespace rus { namespace prover {

LightTree unify(const vector<LightTree>& ex, Subst& sub);

extern bool debug_unify;
extern bool debug_index;

}}}


#pragma once

#include "rus_prover_subst.hpp"

namespace mdl { namespace rus { namespace prover {

FlatTerm unify(const vector<FlatTerm>& ex, FlatSubst& sub);
FlatTerm unify_step(FlatSubst& s, const vector<uint>& vars, const FlatTerm& term);

extern bool debug_unify;
extern bool debug_index;

}}}


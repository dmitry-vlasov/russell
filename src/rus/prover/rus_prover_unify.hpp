#pragma once

#include "rus_prover_subst.hpp"

namespace mdl { namespace rus { namespace prover {

Term unify(const vector<Term>& ex, FlatSubst& sub);
Term unify_step(FlatSubst& s, const vector<uint>& vars, const Term& term);

extern bool debug_unify;
extern bool debug_index;

}}}


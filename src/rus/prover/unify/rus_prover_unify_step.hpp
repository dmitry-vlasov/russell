#pragma once

#include "../rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

Subst unify_step(const Subst& s, const vector<uint>& vars, Term&& term);

}}}}

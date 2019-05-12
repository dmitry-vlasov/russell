#pragma once

#include "../rus_prover_node.hpp"
#include "../unify/rus_prover_unify_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

TermSubst unify_terms(const vector<const Term*>& terms);

}}}}

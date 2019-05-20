#pragma once

#include "../rus_prover_node.hpp"
#include "../unify/rus_prover_unify_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

map<vector<uint>, TermSubst> unify_indexes(const vector<const Index*>& inds);

}}}}

#pragma once

#include "../rus_prover_node.hpp"
#include "../unify/rus_prover_unify_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

map<uint, TermSubst> unify_index_term(const Index& ind, const Term& term);

}}}}

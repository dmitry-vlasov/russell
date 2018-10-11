#pragma once

#include "rus_prover_trie_flat_subst.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

FlatTerm unify(const vector<FlatTerm>& ex, FlatSubst& sub);
FlatTerm unify_step(FlatSubst& s, const vector<LightSymbol>& vars, const FlatTerm& term);
FlatSubst unify_step(const FlatSubst& s, const vector<LightSymbol>& vars, const FlatTerm& term);

extern bool debug_flat_unify;
extern bool debug_flat_index;

}}}}


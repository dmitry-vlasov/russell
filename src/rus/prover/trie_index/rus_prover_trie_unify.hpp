#pragma once

#include "rus_prover_trie_matrix_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

string show(const MultyUnifiedSubs&);
MultyUnifiedSubs unify_subs_matrix(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs);
MultyUnifiedSubs intersect(const map<LightSymbol, vector<VectorUnified>>&, MultyUnifiedSubs& unif);
FlatTerm unify_general(const vector<FlatTerm>& ex, FlatSubst& sub);

extern bool debug_trie_matrix;
extern bool debug_unify_general;

}}}}

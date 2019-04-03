#pragma once

#include "../index/rus_prover_trie_matrix_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

string show(const MultyUnifiedSubs&);
MultyUnifiedSubs unify_subs_matrix(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs);
MultyUnifiedSubs intersect(const map<LightSymbol, vector<VectorUnified>>&, MultyUnifiedSubs& unif);
Term unify_general(const vector<Term>& ex, Subst& sub);

extern bool debug_trie_matrix;
extern bool debug_unify_general;

}}}}
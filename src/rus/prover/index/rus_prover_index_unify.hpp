#pragma once

#include "../rus_prover_limit.hpp"
#include "rus_prover_index_matrix.hpp"

namespace mdl { namespace rus { namespace prover { namespace index {

string show(const MultyUnifiedSubs&);
MultyUnifiedSubs unify_subs_matrix(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& hs, const ProofsSizeLimit*);
Term unify_general(const vector<Term>& ex, Subst& sub);

}}}}

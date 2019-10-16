#pragma once

#include "../rus_prover_limit.hpp"
#include "rus_prover_unify_matrix.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

MultyUnifiedSubs unify_subs_matrix(Prop* pr, Hyp* hy, const vector<ProofExpIndexed>& hs, const ProofsSizeLimit*);
MultyUnifiedSubs unify_subs_matrix(const Subst& common, const vector<vector<SubstInd>>& matr, const ProofsSizeLimit* limit);
Term unify_general(const vector<Term>& ex, Subst& sub);

}}}}

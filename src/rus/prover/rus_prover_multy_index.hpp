#pragma once

#include "rus_prover_index.hpp"

namespace mdl { namespace rus { namespace prover {

typedef map<vector<uint>, Subst> MultyUnifiedSubs;
typedef map<vector<uint>, LightTree> MultyUnifiedTerms;
typedef set<vector<uint>> Restrictions;

MultyUnifiedTerms unify(const vector<const Index*>& mindex, MultyUnifiedSubs& unif, const Restrictions* restrictions = nullptr);

string show(const vector<const Index*>& mindex);

}}}


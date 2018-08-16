#pragma once

#include "rus_prover_index.hpp"

namespace mdl { namespace rus { namespace prover {

typedef map<vector<uint>, Subst> MultyUnifiedSubs;
typedef map<vector<uint>, LightTree> MultyUnifiedTerms;

void unify(
	const vector<const Index*>& mindex,
	MultyUnifiedSubs& unif,
	MultyUnifiedTerms& terms,
	const set<vector<uint>>* restrictions = nullptr);

}}}


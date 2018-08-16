#pragma once

#include "rus_prover_index.hpp"

namespace mdl { namespace rus { namespace prover {

struct MultyIndex {
	typedef map<vector<uint>, Subst> UnifiedSubs;
	typedef map<vector<uint>, LightTree> UnifiedTerms;
	//typedef vector<const Index*> mind;
	//vector<Index> mind;
};

}}}


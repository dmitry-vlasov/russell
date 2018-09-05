#pragma once

#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

vector<Node*> unify_down(Prop* pr, const vector<ProofHypIndexed>& h);
//vector<Node*> unify_down_2(Prop* pr, const ProofHyp* h);

}}}


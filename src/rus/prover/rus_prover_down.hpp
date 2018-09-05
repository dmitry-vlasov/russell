#pragma once

#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

vector<Node*> unify_down(Prop* pr, Hyp* hy, const vector<ProofHypIndexed>& h);

}}}


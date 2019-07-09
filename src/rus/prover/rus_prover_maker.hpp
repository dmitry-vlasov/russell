#pragma once

#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

TheoremWithProof make_theorem_with_proof(const AbstProof& aproof, uint id);
Return test_maker(string theorem);

}}}


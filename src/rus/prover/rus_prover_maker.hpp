#pragma once

#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

unique_ptr<Theorem> make_theorem(const AbstProof& aproof, uint id);
Return test_maker(string theorem);

}}}


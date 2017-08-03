#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

void apply_recursively(const Substitution& sub, rus::Step* step) {
	apply(sub, step->expr);
	for (auto r : step->refs)
		if (r->kind == rus::Ref::STEP) apply_recursively(sub, r->val.step);
}

rus::Ref* ProofHyp::ref() {
	return new rus::Ref(hyp_.get());
}

rus::Step* ProofStep::step() {
	vector<rus::Ref*> refs;
	for (auto ch : child_) refs.push_back(ch->ref());
	const PropRef* p = node_->prop();
	rus::Step* step = new rus::Step(-1, rus::Step::ASS, p->id(), nullptr);
	step->refs = std::move(refs);
	step->expr = *node_->expr();
	apply_recursively(sub_, step);
	return step;
}

rus::Ref* ProofStep::ref() {
	return new rus::Ref(step());
}

rus::Proof* make_proof(rus::Step* step) {

}

}}}


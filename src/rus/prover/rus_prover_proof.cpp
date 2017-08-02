#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

rus::Step* ProofHyp::step() {
	return nullptr;
}

rus::Ref* ProofHyp::ref() {
	if (!ref_) ref_ = new rus::Ref(hyp_.get());
	return ref_;
}

rus::Step* ProofStep::step() {
	if (!step_) {
		vector<rus::Ref*> refs;
		for (auto ch : child_) refs.push_back(ch->ref());
		const PropRef* p = node_->prop();
		step_ = new rus::Step(-1, rus::Step::ASS, p->id(), nullptr);
		step_->refs = std::move(refs);
		step_->expr = *node_->expr();
	}
	return step_;
}

rus::Ref* ProofStep::ref() {
	if (!ref_) ref_ = new rus::Ref(step());
	return ref_;
}

}}}


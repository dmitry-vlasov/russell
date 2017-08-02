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
		Prop* p = prop(node_) ? prop(node_) : prop(node_->parent);
		step_ = new rus::Step(-1, rus::Step::ASS, Assertion::THM, p->prop.assertion()->id(), nullptr);
	}
	return step_;
}

rus::Ref* ProofStep::ref() {
	if (!ref_) ref_ = new rus::Ref(step());
	return ref_;
}

}}}


#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

void apply_recursively(const Substitution& sub, rus::Step* step) {
	apply(sub, step->expr);
	for (auto& r : step->refs) {
		if (r.get()->kind() == rus::Ref::STEP) apply_recursively(sub, r.get()->step());
	}
}

rus::Ref* ProofHyp::ref() {
	return new rus::Ref(hyp_.get());
}

rus::Step* ProofStep::step() {
	vector<unique_ptr<rus::Ref>> refs;
	for (auto ch : child_) refs.emplace_back(ch->ref());
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

static void fill_in_proof(rus::Step* step, rus::Proof* proof) {
	for (auto& r : step->refs) {
		if (r.get()->kind() == rus::Ref::STEP)
			fill_in_proof(r.get()->step(), proof);
	}
	for (auto& s : step->expr.symbols) {
		if (s.kind() != Symbol::VAR) continue;
		if (proof->allvars.isDeclared(s)) continue;
		if (proof->theorem()->vars.isDeclared(s)) continue;
		proof->allvars.v.push_back(s);
	}
	step->set_ind(proof->elems.size());
	proof->elems.emplace_back(unique_ptr<Step>(step));
}

rus::Proof* make_proof(rus::Step* step, uint th, rus::Prop* prop) {
	rus::Proof* ret = new rus::Proof(th);
	fill_in_proof(step, ret);
	ret->elems.emplace_back(unique_ptr<Qed>(new Qed(prop, step)));
	return ret;
}

}}}


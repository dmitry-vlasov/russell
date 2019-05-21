#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>

namespace mdl { namespace rus {

unique_ptr<Proof> reduce_duplcate_steps(const Proof* proof) {
	unique_ptr<Proof> ret = make_unique<Proof>(
		proof->thm.id(),
		proof->id(),
		proof->token
	);
	prover::unify::Index expressions;
	for (const auto& e : proof->elems) {
		if (Proof::kind(e) == Proof::STEP) {
			const Step* step = Proof::step(e);
			prover::Term term = prover::Tree2FlatTerm(*step->expr.tree());
			const vector<uint>* previous = expressions.findTerm(term);
			if (previous && previous->size()) {
				uint prev = previous->at(0);
			} else {
				ret->elems.emplace_back(make_unique<Step>(
					step->ind_, step->kind(), step->ass_id(), ret.get(), step->token
				));
				expressions.add(term, step->ind_);
			}
		}
	}
	return ret;
}

}} // mdl::rus

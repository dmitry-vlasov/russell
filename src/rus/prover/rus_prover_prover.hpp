#pragma once

#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

struct Prover : public Space {
	typedef vector<unique_ptr<rus::Proof>> Proved;
	template<class T>
	using IndexMap = unify::IndexMap<T>;

	Prover(rus::Qed*, Tactic*);
	Prover(rus::Assertion*, rus::Prop*, Tactic*);

	void registerNode(Node* n) {
		Space::registerNode(n);
		if (Hyp* h = dynamic_cast<Hyp*>(n)) {
			if (!expressions_.find(h->expr).size()) {
				expressions_.add(h->expr, h);
			}
		}
	}
	void unregisterNode(Node* n) {
		Space::unregisterNode(n);
		// TODO:
	}

	void buildUp(Node* n) override;
	void initProofs(Hyp* h, const rus::Hyp* hint = nullptr) override;
	uint theoremId() const override { return prop_.id(); }
	Proved proved();

private:
	void buildUpProp(Prop*);
	void buildUpHyp(Hyp*);

	PropRef           prop_;
	IndexMap<HypRef>  hyps_;
	IndexMap<PropRef> assertions_;
	IndexMap<Hyp*>    expressions_;
};

Return test_with_oracle(string theorem, uint max_proofs, uint max_proof_len);

}}}


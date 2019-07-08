#pragma once

#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

struct Ass {
	vector<unique_ptr<rus::Hyp>> hyps;
	unique_ptr<rus::Prop> prop;
	string show() const {
		ostringstream oss;
		for (const auto& h : hyps) {
			oss << *h << endl;
		}
		oss << "--------------" << endl;
		oss << *prop << endl;
		return oss.str();
	}
};

struct Thm {
	Ass ass;
	unique_ptr<rus::Proof> proof;
	string show() const {
		ostringstream oss;
		oss << ass.show() << endl;
		oss << *proof << endl;
		return oss.str();
	}
};

struct Maker : public Space {
	typedef vector<unique_ptr<rus::Proof>> Proved;
	template<class T>
	using IndexMap = unify::IndexMap<T>;

	Maker(const AbstProof& aproof, uint id);

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

	unique_ptr<Thm> make();

	void buildUp(Node* n) override;
	void initProofs(Hyp* h, const rus::Hyp* hint = nullptr) override;
	uint theoremId() const override { return theorem_id_; }

private:
	void expandUp(uint index, set<Node*>& leafs);

	void buildUpProp(Prop*);
	void buildUpHyp(Hyp*);

	uint theorem_id_;
	const AbstProof& abst_proof_;

	IndexMap<unique_ptr<rus::Hyp>> hyps_;
	IndexMap<PropRef>  assertions_;
	IndexMap<Hyp*>     expressions_;
};

Return test_maker(string theorem);

}}}


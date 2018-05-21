#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

inline uint find_index(const rus::Assertion* a, const rus::Prop* p) {
	uint c = 0;
	for (auto& x : a->props) if (x.get() == p) return c; else ++c;
	throw Error("prop is not found");
}

Space::Space(rus::Qed* q, Tactic* t) :
	Space(q->step->proof()->thm.get(), q->prop, t) {
}

Space::Space(rus::Assertion* a, rus::Prop* p, Tactic* t) :
	root(nullptr), prop(a, find_index(a, p)), tactic_(t) {
	uint c = 0;
	for (auto& p : prop.assertion()->props) {
		hyps.add(p.get()->expr.tree(), HypRef(a, c++));
	}
	root = new Hyp(std::move(create_non_replaceable(p->expr)), this);
	buildUp(root);
}

void Space::buildUp(Node* n) {
	for (auto m : n->buildUp()) m->buildUp();
}

rus::Proof* Space::prove() {
	while (Node* n = tactic_->next()) {
		buildUp(n);
		if (rus::Proof* ret = checkProved()) {
			return ret;
		}
	}
	return nullptr;
}

void delete_steps_recursively(rus::Step* s) {
	for (auto& r : s->refs) {
		if (r.get()->kind() == rus::Ref::STEP) {
			delete_steps_recursively(r.get()->step());
		}
	}
	delete s;
}

rus::Proof* Space::checkProved() {
	if (!root->proof.size()) return nullptr;
	for (auto& p : root->proof) {
		if (ProofStep* ps = dynamic_cast<ProofStep*>(p)) {
			rus::Step* s = ps->step();
			if (rus::Proof* pr = make_proof(s, prop.assertion()->id(), prop.get())) {
				if (pr->check()) return pr;
			}
			delete_steps_recursively(s);
		}
		delete p;
	}
	root->proof.clear();
	return nullptr;
}

Space* Space::instance = nullptr;

}}}


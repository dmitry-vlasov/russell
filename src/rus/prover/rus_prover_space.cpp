#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

inline uint find_index(const rus::Assertion* a, const rus::Prop* p) {
	uint c = 0;
	for (auto x : a->props) if (x == p) return c; else ++c;
	throw Error("prop is not found");
}

Space::Space(rus::Qed* q) :	Space(q->step->proof()->thm, q->prop) {
}

Space::Space(rus::Assertion* a, rus::Prop* p) :
	root(p->expr, this), prop(a, find_index(a, p)) {
	uint c = 0;
	for (rus::Prop* p : prop.assertion()->props) {
		hyps.add(p->expr.tree, HypRef(a, c++));
	}
	make_non_replaceable(root.expr_);
}

void Space::buildUp(Hyp* h) {
	for (auto p : h->buildUp()) p->buildUp();
}

void Space::buildUp(Prop* p) {
	for (auto h : p->buildUp()) h->buildUp();
}

}}}


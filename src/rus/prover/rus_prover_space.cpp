#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

Space::Space(rus::Qed* q) : root(q->prop->expr, this) {
	Assertion* a = q->step->proof()->thm;
	uint c = 0;
	for (;c < a->props.size(); ++ c)
		if (a->props[c] == q->prop) break;
	assert(c < ass->props.size());
	prop = PropRef {a, c};
	c = 0;
	for (rus::Prop* p : a->props) {
		hyps.add(p->expr.tree, HypRef{a, c++});
	}
}

void Space::buildUp(Hyp* h) {
	for (auto p : h->buildUp()) p->buildUp();
}

void Space::buildUp(Prop* p) {
	for (auto h : p->buildUp()) h->buildUp();
}

}}}


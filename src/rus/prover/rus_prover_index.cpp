#include "rus_prover.hpp"

namespace mdl { namespace rus { namespace prover {

Index<PropRef>& assertion_index() {
	static Index<PropRef> index;
	return index;
}

void add_to_index(Assertion* a) {
	uint c = 0;
	for (rus::Prop* p : a->props) {
		assertion_index().add(p->expr.tree.get(), PropRef{a, c++});
	}
}

}}}

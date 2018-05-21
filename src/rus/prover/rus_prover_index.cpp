#include "rus_prover_index.hpp"

namespace mdl { namespace rus { namespace prover {

Index<PropRef>& assertion_index() {
	static map<uint, Index<PropRef>> index;
	return index[Sys::get().id];
}

void add_to_index(Assertion* a) {
	uint c = 0;
	for (auto& p : a->props) {
		assertion_index().add(p.get()->expr.tree(), PropRef(a, c++));
	}
}

void add_to_index(Proof* a) {
	// TODO: implement
}

}}}

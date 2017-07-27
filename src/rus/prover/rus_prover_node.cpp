#include "rus_prover.hpp"

namespace mdl { namespace rus { namespace prover {

Index<Assertion>& assertion_index();

vector<Node*> build_up(Node* n) {
	vector<Node*> ret;
	switch (n->kind()) {
	case Node::REF: break;
	case Node::HYP: {
		for (auto p : assertion_index().unify(hyp(n)->expr))
			ret.push_back(new Prop(p.data, p.sub, n));
		break;
	}
	case Node::PROP:
		for (rus::Hyp* h : prop(n)->ass->hyps)
			ret.push_back(new Hyp(h->expr, n));
		break;
	}
	return ret;
}


}}}


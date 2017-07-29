#include "rus_prover.hpp"

namespace mdl { namespace rus { namespace prover {

vector<Node*> build_up(Node* n) {
	vector<Node*> ret;
	switch (n->kind()) {
	case Node::REF: break;
	case Node::HYP: {
		for (const auto& p : assertion_index().unify(hyp(n)->expr.tree.get()))
			ret.push_back(new Prop(p.first, p.second, n));
		break;
	}
	case Node::PROP:
		for (rus::Hyp* h : prop(n)->prop.ass.get()->hyps)
			ret.push_back(new Hyp(h->expr, n));
		break;
	}
	return ret;
}


}}}


#include "rus_prover.hpp"

namespace mdl { namespace rus { namespace prover {

vector<Node*> build_up(Node* n, const Assertion* a) {
	vector<Node*> ret;
	switch (n->kind()) {
	case Node::ROOT:
	case Node::HYP:
	case Node::PROP:
	case Node::REF:;
	}
	return ret;
}

}}}


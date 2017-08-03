#include "rus_prover_tactics.hpp"

namespace mdl { namespace rus { namespace prover {

/*
static rus::Step* root_step(rus::Proof* p) {
	for (auto e : p->elems) {
		if (e.kind == Proof::Elem::QED) {
			return e.val.qed->step;
		}
	}
	return nullptr;
}
*/
Oracle::Oracle(rus::Proof* p) : proof(p), root((*p->qeds().begin())->step) { }

void Oracle::add(Node* n) {
	if (Prop* p = dynamic_cast<Prop*>(n)) {
		const Assertion* ass = p->prop()->assertion();
		cout << endl << "orcale observing: " << show_id(ass->id()) << " ";
		if (props.empty()) {
			if (ass == root->ass()) {
				leafs.push_back(p);
				props[p] = root;
			}
		} else {
			if (p->parent && p->parent->parent) {
				Prop* grand = dynamic_cast<Prop*>(p->parent->parent);
				if (props.count(grand)) {
					rus::Step* st = props.at(grand);
					for (auto r : st->refs) {
						if (r->kind == rus::Ref::STEP && ass == r->val.step->ass()) {
							leafs.push_back(p);
							props[p] = r->val.step;
						}
					}
				}
			}
		}
	}
}


}}}


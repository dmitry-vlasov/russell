#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

void apply_recursively(const Substitution& sub, rus::Step* step) {
	step->expr = apply(sub, step->expr);
	for (auto& r : step->refs) {
		if (r.get()->kind() == rus::Ref::STEP) {
			apply_recursively(sub, r.get()->step());
		}
	}
}

ProofHyp::ProofHyp(Hyp& h, const Subst& s) :
	ProofNode(s), node(h) {
}

ProofHyp::~ProofHyp() {
	for (auto p : parents) {
		uint i = find_in_vector(p->node.proofs, p);
		if (i != -1) {
			p->node.proofs.erase(p->node.proofs.begin() + i);
		}
	}
}

ProofTop::ProofTop(Hyp& n, const HypRef& h, const Subst& s) : ProofHyp(n, s), hyp(h) {
	expr = convert_tree(*h.get()->expr.tree(), ReplMode::DENY_REPL);
}

rus::Ref* ProofExp::ref() {
	return child->ref();
}

rus::Ref* ProofTop::ref() {
	return new rus::Ref(hyp.get());
}

ProofExp::ProofExp(Hyp& n, ProofProp* c, const Subst& s) :
	ProofHyp(n, s), child(c) {
	child->parent = this;
	expr = apply(s, n.expr);
}

ProofProp::ProofProp(Prop& n, const vector<ProofHyp*>& p, const Subst& s) :
	ProofNode(s), parent(nullptr), node(n), premises(p) {
	for (auto p : premises) {
		p->parents.push_back(this);
	}
}

ProofProp::~ProofProp() {
	if (parent) {
		uint i = find_in_vector(parent->node.proofs, parent);
		assert(i != -1);
		parent->node.proofs.erase(parent->node.proofs.begin() + i);
	}
}

rus::Step* ProofProp::step() {
	vector<unique_ptr<rus::Ref>> refs;
	for (auto ch : premises) {
		refs.emplace_back(ch->ref());
	}
	const PropRef& p = node.prop;
	rus::Step* step = new rus::Step(-1, rus::Step::ASS, p.id(), nullptr);
	step->refs = std::move(refs);
	step->expr = std::move(convert_expr(parent->node.expr));
	Substitution s = convert_sub(sub);
	apply_recursively(s, step);
	return step;
}

rus::Ref* ProofProp::ref() {
	return new rus::Ref(step());
}

static void fill_in_proof(rus::Step* step, rus::Proof* proof) {
	for (auto& r : step->refs) {
		if (r.get()->kind() == rus::Ref::STEP)
			fill_in_proof(r.get()->step(), proof);
	}
	for (auto& s : step->expr.symbols) {
		if (s.kind() != Symbol::VAR) continue;
		if (proof->allvars.isDeclared(s)) continue;
		if (proof->theorem()->vars.isDeclared(s)) continue;
		proof->allvars.v.push_back(s);
	}
	step->proof_ = proof;
	step->set_ind(proof->elems.size());
	proof->elems.emplace_back(unique_ptr<Step>(step));
}

rus::Proof* make_proof(rus::Step* step, uint theorem, rus::Prop* prop) {
	rus::Proof* ret = new rus::Proof(theorem);
	ret->inner = true;
	fill_in_proof(step, ret);
	ret->elems.emplace_back(unique_ptr<Qed>(new Qed(prop, step)));
	ret->verify(VERIFY_SUB);
	try {
		ret->verify(VERIFY_DISJ);
	} catch (Error& err) {
		delete ret;
		ret = nullptr;
	}
	return ret;
}

}}}


#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

void apply_recursively(const Substitution& sub, rus::Step* step) {
	step->expr = apply(sub, step->expr);
	for (auto& r : step->refs) {
		if (r.get()->kind() == rus::Ref::STEP) {
			apply_recursively(sub, r.get()->step());
		}
	}
}

static uint proof_node_index = 0;

ProofNode::ProofNode(const Subst& s) :
	sub(s), new_(true), ind(proof_node_index++) { }

ProofHyp::ProofHyp(Hyp& h, const Subst& s, const LightTree& e) :
	ProofNode(s), node(h), expr(e) {
}

ProofHyp::~ProofHyp() {
	for (auto p : parents) {
		uint i = find_in_vector(p->node.proofs, p);
		if (i != -1) {
			p->node.proofs.erase(p->node.proofs.begin() + i);
		}
	}
}

ProofTop::ProofTop(Hyp& n, const HypRef& h, const Subst& s) :
	ProofHyp(n, s, apply(s, convert_tree(*h.get()->expr.tree(), ReplMode::DENY_REPL, LightSymbol::MATH_INDEX))), hyp(h) {
}

bool ProofTop::equal(const ProofNode* n) const {
	if (const ProofTop* t = dynamic_cast<const ProofTop*>(n)) {
		return hyp == t->hyp && &node == &t->node;
	} else {
		return false;
	}
}

rus::Ref* ProofTop::ref() const {
	return new rus::Ref(hyp.get());
}


rus::Ref* ProofExp::ref() const {
	return child->ref();
}

rus::Proof* ProofExp::proof() const {
	return child->proof();
}

bool ProofExp::equal(const ProofNode* n) const {
	if (const ProofExp* e = dynamic_cast<const ProofExp*>(n)) {
		return &node == &e->node && child->equal(e->child);
	} else {
		return false;
	}
}


string show_struct(const ProofNode* n);

ProofExp::ProofExp(Hyp& h, ProofProp* c, const Subst& s) :
	ProofHyp(h, s, apply(s, h.expr)), child(c) {
	child->parent = this;
	child->new_ = false;
	try {
		rus::Proof* pr = proof();
		//cout << "PROOF: " << *pr << endl;
		delete pr;
	} catch (Error& err) {
		cout << "ERR proof: " << ind << endl;
		cout << show_struct(this) << endl;
		throw err;
	}

}

ProofProp::ProofProp(Prop& n, const vector<ProofHyp*>& p, const Subst& s) :
	ProofNode(s), parent(nullptr), node(n), premises(p) {
	for (auto p : premises) {
		p->parents.push_back(this);
		p->new_ = false;
	}
	if (n.prop.ass->arity() > 0) {
		Subst s0 = premises[0]->sub;
		compose(s0, sub);
		for (uint i = 0; i < premises.size(); ++ i) {
			Subst si = premises[i]->sub;
			compose(si, sub);
			if (s0 != si) {
				string err;
				err += "s0 != s" + to_string(i) + "\n";
				err += "s0: " +  prover::show(s0) + "\n";
				err += "s" + to_string(i) + ": " + prover::show(si) + "\n\n";
				err += "orig s0: " +  prover::show(premises[0]->sub) + "\n";
				err += "orig s" + to_string(i) + ": " + prover::show(premises[i]->sub) + "\n";
				err += "unifier:\n";
				err += prover::show(s) + "\n";
				throw Error(err);
			}
		}
	}

}

ProofProp::~ProofProp() {
	if (parent) {
		uint i = find_in_vector(parent->node.proofs, parent);
		assert(i != -1);
		parent->node.proofs.erase(parent->node.proofs.begin() + i);
	}
}

bool ProofProp::equal(const ProofNode* n) const {
	if (const ProofProp* p = dynamic_cast<const ProofProp*>(n)) {
		if (premises.size() != p->premises.size()) {
			return false;
		}
		for (int i = 0; i < premises.size(); ++ i) {
			if (!premises[i]->equal(p->premises[i])) {
				return false;
			}
		}
		return &node == &p->node;
	} else {
		return false;
	}
}

rus::Step* ProofProp::step() const {
	if (!parent) return nullptr;
	vector<unique_ptr<rus::Ref>> refs;
	for (auto ch : premises) {
		refs.emplace_back(ch->ref());
	}
	const PropRef& p = node.prop;
	rus::Step* step = new rus::Step(-1, rus::Step::ASS, p.id(), nullptr);
	step->refs = std::move(refs);
	step->expr = std::move(convert_expr(parent->expr));
	Substitution s = convert_sub(sub);
	apply_recursively(s, step);
	return step;
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

rus::Proof* ProofProp::proof() const {
	rus::Step* st = step();
	rus::Proof* ret = new rus::Proof(node.space->prop.ass->id());
	ret->inner = true;
	fill_in_proof(st, ret);
	ret->elems.emplace_back(unique_ptr<Qed>(new Qed(node.space->prop.get(), st)));
	try {
		ret->verify(VERIFY_SUB);
	} catch (Error& err) {
		cout << "WRONG PROOF:" << endl;
		ostringstream oss;
		ret->write(oss);
		cout << oss.str() << endl;
		throw err;
	}
	try {
		ret->verify(VERIFY_DISJ);
	} catch (Error& err) {
		delete ret;
		cout << "ret->verify(VERIFY_DISJ)  FAILED:" << endl;
		cout << err.msg << endl;
		ret = nullptr;
	}
	return ret;
}

rus::Ref* ProofProp::ref() const {
	return new rus::Ref(step());
}


}}}


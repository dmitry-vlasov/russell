#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

static void apply_recursively(const Substitution& sub, rus::Step* step) {
	step->expr = apply(sub, step->expr);
	for (auto& r : step->refs) {
		if (r.get()->kind() == rus::Ref::STEP) {
			apply_recursively(sub, r.get()->step());
		}
	}
}

ProofTop::ProofTop(Hyp& n, const HypRef& hy, const Subst& s, bool hi) :
	ProofExp(s, hi), node(n), hyp(hy),
	expr_(s.apply(Tree2Term(*hy.get()->expr.tree(), ReplMode::DENY_REPL, LightSymbol::MATH_INDEX))) {
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


rus::Ref* ProofHyp::ref() const {
	return child->ref();
}

rus::Proof* ProofHyp::proof() const {
	return child->proof();
}

bool ProofHyp::equal(const ProofNode* n) const {
	if (const ProofHyp* e = dynamic_cast<const ProofHyp*>(n)) {
		return &node == &e->node && child->equal(e->child);
	} else {
		return false;
	}
}

rus::Ref* ProofRef::ref() const {
	return child->ref();
}

rus::Proof* ProofRef::proof() const {
	return child->proof();
}

bool ProofRef::equal(const ProofNode* n) const {
	if (const ProofRef* r = dynamic_cast<const ProofRef*>(r)) {
		return &node == &r->node && child->equal(r->child);
	} else {
		return false;
	}
}

string show_struct(const ProofNode* n);

//#define VERIFY_PROOF_EXP

ProofHyp::ProofHyp(Hyp& hy, ProofNode* c, const Subst& s, bool hi) :
	ProofExp(s, hi), child(c), node(hy), expr_(s.apply(hy.expr)) {
	child->addParent(this);
	child->new_ = false;
#ifdef VERIFY_PROOF_EXP
	try {
		rus::Proof* pr = proof();
		//cout << "PROOF: " << *pr << endl;
		delete pr;
	} catch (Error& err) {
		cout << "ERR proof: " << ind << endl;
		cout << show_struct(this) << endl;
		throw err;
	}
#endif
}

ProofHyp::ProofHyp(Hyp& hy, ProofNode* c, Subst&& s, bool hi) :
	ProofExp(s, hi), child(c), node(hy), expr_(s.apply(hy.expr)) {
	child->addParent(this);
	child->new_ = false;
#ifdef VERIFY_PROOF_EXP
	try {
		rus::Proof* pr = proof();
		//cout << "PROOF: " << *pr << endl;
		delete pr;
	} catch (Error& err) {
		cout << "ERR proof: " << ind << endl;
		cout << show_struct(this) << endl;
		throw err;
	}
#endif
}

//#define VERIFY_PROOF_PROP

ProofProp::ProofProp(Prop& n, const vector<ProofExp*>& p, const Subst& s, bool h) :
	ProofNode(s, h), parent(nullptr), node(n), premises(p) {
	for (auto p : premises) {
		p->addParent(this);
		p->new_ = false;
	}
#ifdef VERIFY_PROOF_PROP
	if (n.prop.ass->arity() > 0) {
		Subst s0 = premises[0]->sub;
		s0.compose(sub, CompMode::NORM, false);
		for (uint i = 0; i < premises.size(); ++ i) {
			Subst si = premises[i]->sub;
			si.compose(sub, CompMode::NORM, false);
			if (s0 != si) {
				string err;
				err += "s0 != s" + to_string(i) + "\n";
				err += "diff: " + show_diff(s0, si) + "\n";
				err += "s0: " +  s0.show() + "\n";
				err += "s" + to_string(i) + ": " + si.show() + "\n\n";
				err += "orig s0: " + premises[0]->sub.show() + "\n";
				err += "orig s" + to_string(i) + ": " + premises[i]->sub.show() + "\n";
				err += "unifier:\n";
				err += s.show() + "\n";
				throw Error(err);
			}
		}
	}
#endif
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
	if (!parent) {
		throw Error("no parent");
	}
	vector<unique_ptr<rus::Ref>> refs;
	for (auto ch : premises) {
		refs.emplace_back(ch->ref());
	}
	const PropRef& p = node.prop;
	rus::Step* step = new rus::Step(-1, rus::Step::ASS, p.id(), nullptr);
	step->refs = std::move(refs);
	step->expr = std::move(Term2Expr(parent->expr()));
	Substitution s = Subst2Substitution(sub);
	apply_recursively(s, step);
	return step;
}

void fill_in_proof(rus::Step* step, rus::Proof* proof) {
	for (auto& r : step->refs) {
		if (r.get()->kind() == rus::Ref::STEP)
			fill_in_proof(r.get()->step(), proof);
	}
	for (auto& s : step->expr.symbols) {
		if (const Var* v = dynamic_cast<const Var*>(s.get())) {
			if (proof->allvars.isDeclared(v->lit())) continue;
			if (proof->theorem()->vars.isDeclared(v->lit())) continue;
			proof->allvars.v.push_back(*v);
		}
	}
	step->proof_ = proof;
	step->set_ind(proof->elems.size());
	proof->elems.emplace_back(unique_ptr<Step>(step));
}

rus::Proof* ProofProp::proof() const {
	rus::Step* st = step();
	rus::Proof* ret = new rus::Proof(node.space->prop().ass->id());
	ret->inner = true;
	fill_in_proof(st, ret);
	ret->elems.emplace_back(unique_ptr<Qed>(new Qed(node.space->prop().get(), st)));
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
		ret = nullptr;
	}
	return ret;
}

rus::Ref* ProofProp::ref() const {
	return new rus::Ref(step());
}


}}}


#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

static void apply_recursively(const Substitution& sub, rus::Step* step, set<const Writable*>& visited) {
	step->expr = apply(sub, step->expr);
	for (auto& r : step->refs) {
		if (rus::Step* s = r.get()->step()) {
			if (!visited.count(s)) {
				visited.insert(s);
				apply_recursively(sub, s, visited);
			}
		} else if (rus::Hyp* h = r.get()->hyp()) {
			if (!visited.count(h)) {
				visited.insert(h);
				h->expr = apply(sub, h->expr);
			}
		}
	}
}

static void apply_recursively(const Substitution& sub, rus::Step* step) {
	set<const Writable*> visited;
	apply_recursively(sub, step, visited);
}

// ProofTop -------------------------

ProofTop::ProofTop(const Hyp& n, rus::Hyp* hy, const Subst& s, bool hi) :
	ProofExp(s, hi), node(n), hyp(hy),
	expr_(s.apply(Tree2Term(*hy->expr.tree(), false))) {
}

bool ProofTop::equal(const ProofNode* n) const {
	if (const ProofTop* t = dynamic_cast<const ProofTop*>(n)) {
		return hyp == t->hyp && &node == &t->node;
	} else {
		return false;
	}
}

// ProofHyp -------------------------

bool ProofHyp::equal(const ProofNode* n) const {
	if (const ProofHyp* e = dynamic_cast<const ProofHyp*>(n)) {
		return &node == &e->node && child->equal(e->child);
	} else {
		return false;
	}
}

//#define VERIFY_PROOF_HYP

ProofHyp::ProofHyp(const Hyp& hy, ProofNode* c, const Subst& s, bool hi) :
	ProofExp(s, hi), child(c), node(hy), expr_(s.apply(hy.expr)) {
	child->addParent(this);
	child->new_ = false;
#ifdef VERIFY_PROOF_HYP
	try {
		auto pr = gen_proof(this);
		//cout << "PROOF: " << *pr << endl;
	} catch (Error& err) {
		cout << "ERR proof: " << ind << endl;
		cout << show_proof_struct(this) << endl;
		cout << endl;
		//cout << show_nodes_struct(&node) << endl;
		throw err;
	}
#endif
}

ProofHyp::ProofHyp(const Hyp& hy, ProofNode* c, Subst&& s, bool hi) :
	ProofExp(s, hi), child(c), node(hy), expr_(s.apply(hy.expr)) {
	if (!child) {
		throw Error("!child ProofHyp::ProofHyp");
	}
	child->addParent(this);
	child->new_ = false;
#ifdef VERIFY_PROOF_HYP
	try {
		auto pr = gen_proof(this);
		//cout << "PROOF: " << *pr << endl;
	} catch (Error& err) {
		cout << "ERR proof: " << ind << endl;
		cout << show_proof_struct(this) << endl;
		cout << endl;
		//cout << show_nodes_struct(&node) << endl;
		throw err;
	}
#endif
}



// ProofRef -------------------------

static set<LightSymbol> vars_in_subst_image(const Subst& sub) {
	set<LightSymbol> vars;
	for (const auto& p : sub) {
		for (const auto& v : p.second.term.vars()) {
			vars.insert(v);
		}
	}
	return vars;
}

ProofRef::ProofRef(const Ref& n, ProofExp* c, bool hi) :
	ProofExp(n.repl.direct().subst(), hi), node(n), child(c) {
	sub.compose(child->sub, CompMode::SEMI);
	set<LightSymbol> s_im_vars = vars_in_subst_image(child->sub);
	for (auto v : s_im_vars) {
		sub.compose(v, n.space->vars().makeFreshVar(v.lit, v.type), CompMode::SEMI);
	}
}

bool ProofRef::equal(const ProofNode* n) const {
	if (const ProofRef* r = dynamic_cast<const ProofRef*>(r)) {
		return &node == &r->node && child->equal(r->child);
	} else {
		return false;
	}
}

//#define VERIFY_PROOF_PROP

// ProofProp -------------------------

ProofProp::ProofProp(const Prop& n, const vector<ProofExp*>& p, const Subst& s, bool h) :
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
				err += show_proof_struct(this);
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









struct ProofEnv {
	ProofEnv() : proof(make_unique<rus::Proof>()) {
		proof->inner = true;
	}

	void genSteps(const ProofNode* n) {
		if (const ProofHyp* h = dynamic_cast<const ProofHyp*>(n)) {
			if (h->child) genSteps(h->child);
		} else if (const ProofRef* r = dynamic_cast<const ProofRef*>(n)) {
			if (r->child) genSteps(r->child);
		} else if (const ProofTop* t = dynamic_cast<const ProofTop*>(n)) {
			if (!refMap.count(t)) {
				refMap.emplace(t, rus::Ref(t->hyp));
			}
		} else if (const ProofProp* p = dynamic_cast<const ProofProp*>(n)) {
			if (!stepMap.count(p) && p->parent) {
				for (auto prem : p->premises) {
					genSteps(prem);
				}
				rus::Step* step = new rus::Step(proof->steps.size(), rus::Step::ASS, p->node.prop.id(), proof.get());
				for (auto prem : p->premises) {
					step->refs.emplace_back(make_unique<rus::Ref>(getRef(prem)));
				}
				step->expr = std::move(Term2Expr(p->parent->expr()));
				step->set_ind(proof->steps.size());
				apply_recursively(Subst2Substitution(p->sub), step);
				stepMap.emplace(p, step);
				refMap.emplace(p, rus::Ref(step));
				proof->steps.emplace_back(unique_ptr<Step>(step));
			}
		} else {
			throw Error("Impossible ProofNode type");
		}
	}
	unique_ptr<rus::Proof> proof;

	/*void internalVars() {
		for (auto& e : proof->elems) {
			if (rus::Step* step = rus::Proof::step(e)) {
				for (auto& s : step->expr.symbols) {
					if (const Var* v = dynamic_cast<const Var*>(s.get())) {
						if (proof->allvars.isDeclared(v->lit())) continue;
						if (proof->theorem()->vars.isDeclared(v->lit())) continue;
						proof->allvars.v.push_back(*v);
					}
				}
			}
		}
	}*/

private:
	const rus::Ref& getRef(const ProofNode* n) {
		if (refMap.count(n)) {
			return refMap.at(n);
		} else if (const ProofHyp* h = dynamic_cast<const ProofHyp*>(n)) {
			if (h->child) return getRef(h->child); else throw Error("undefined reference to:\n" + n->show());
		} else if (const ProofRef* r = dynamic_cast<const ProofRef*>(n)) {
			if (r->child) return getRef(r->child); else throw Error("undefined reference to:\n" + n->show());
		} else {
			throw Error("undefined reference to:\n" + n->show());
		}
	}
	map<const ProofProp*, rus::Step*> stepMap;
	map<const ProofNode*, rus::Ref> refMap;
};

bool debug_gen_proof = false;

unique_ptr<rus::Proof> gen_proof(const ProofNode* n) {
	if (const ProofHyp* h = dynamic_cast<const ProofHyp*>(n)) {
		return gen_proof(h->child);
	} else if (const ProofRef* r = dynamic_cast<const ProofRef*>(n)) {
		return gen_proof(r->child);
	} else if (const ProofProp* p = dynamic_cast<const ProofProp*>(n)) {
		ProofEnv env;
		env.genSteps(p);
		try {
			env.proof->verify(VERIFY_SUB);
		} catch (Error& err) {
			cout << "WRONG PROOF:" << endl;
			ostringstream oss;
			oss << show_proof_struct(n) << endl;
			env.proof->write(oss);
			cout << oss.str() << endl;
			throw err;
		}
		try {
			env.proof->verify(VERIFY_DISJ);
		} catch (Error& err) {
			//if (debug_gen_proof) {
			//	cout << "!env.proof->verify(VERIFY_DISJ)" << endl;
			//}
			env.proof.reset();
		}
		return std::move(env.proof);
	} else {
		throw Error("Impossible ProofNode type");
	}
}

void traverseProof(ProofNode* root, std::function<void(ProofNode*)> f) {
	stack<ProofNode*> st;
	st.push(root);
	while (!st.empty()) {
		ProofNode* n = st.top();
		st.pop();
		f(n);
		if (ProofHyp* h = dynamic_cast<ProofHyp*>(n)) {
			if (h->child) {
				st.push(h->child);
			}
		} else if (ProofRef* r = dynamic_cast<ProofRef*>(n)) {
			if (r->child) {
				st.push(r->child);
			}
		} else if (ProofProp* p = dynamic_cast<ProofProp*>(n)) {
			for (auto c : p->premises) {
				if (c) {
					st.push(c);
				}
			}
		}
	}
}

}}}


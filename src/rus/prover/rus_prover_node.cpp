#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

Node::~Node() {
	space->unregisterNode(this);
}

static Subst make_free_vars_fresh(const Assertion* a, Space* space, set<uint>& assertion_vars, const Subst& s) {
	Subst ret;
	for (const auto& w : a->vars.v) {
		LightSymbol v(w, ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX);
		if (!ret.maps(v)) {
			if (!s.maps(v)) {
				uint i = space->hasVar(v.lit) ? space->getVar(v.lit) + 1 : LightSymbol::INTERNAL_MIN_INDEX;
				space->setVar(v.lit, i);
				ret.compose(v, Term(LightSymbol(w, ReplMode::KEEP_REPL, i)));
			}
		}
		assertion_vars.insert(v.lit);
	}
	return ret;
}

Ref::Ref(Hyp* p, Hyp* a, Space* s, VarRepl&& r) :
	Node(s), parent(p), ancestor(a), repl(std::move(r)) {
	space->registerNode(this);
	ancestor->parents.push_back(this);
	cout << "Ref is built, parent: " << p->ind << " = " << p->expr << ", child: " << a->ind << " = " << a->expr << endl;
	cout << "var repl:" << endl;
	cout << repl.show() << endl;
}

bool Ref::buildDown(set<Node*>& downs) {
	bool new_proofs = false;
	for (const auto& p : proofs) {
		if (p->new_) {
			ProofHyp* parent_proof = new ProofHyp(*parent, p.get(), p->sub, p->hint);
#ifdef VERIFY_UNIQUE_PROOFS
			if (parent->proofs.size() < 64) {
				// Don't check ALL proofs if there's too much (43050 for example)
				for (auto& h : parent->proofs) {
					if (hp->equal(h.get())) {
						cout << "DUPLICATE EXP PROOF" << endl;
						cout << hp->show() << endl;
						cout << "-----------" << endl;
						cout << h->show() << endl;
					}
				}
			}
#endif
			parent->proofs.emplace_back(parent_proof);

			try {
				if (rus::Proof* rus_proof = parent_proof->proof()) {
					delete rus_proof;
				}
			} catch (Error& err) {
				cout << "FUCK 2)" << endl;
				cout << "THIS: " << endl << show() << endl;
				//cout << "PARENT: " << endl << ref->show() << endl;
				//cout << "proof: " << p.proof->show() << endl;
				throw err;
			}

			new_proofs = true;
		}
	}
	if (new_proofs) {
		downs.insert(parent);
	}
	return new_proofs;
}

Hyp::Hyp(Term&& e, Space* s) :
	Node(s), expr(std::move(e)) {
	space->registerNode(this);
}

Hyp::Hyp(Term&& e, Prop* p) :
	Node(p), expr(std::move(e)) {
	parents.push_back(p);
	space->registerNode(this);
}

void Hyp::buildUp() {
	Timer timer1;
	Timer timer;
	auto unified = space->assertions().unify(expr);
	add_timer_stats("build_up_hyp_unify_timer", timer);
	timer.start();
	for (auto& m : unified) {
		set<uint> assertion_vars;
		Subst fresher = make_free_vars_fresh(m.data.ass, space, assertion_vars, m.sub);
		for (const auto& p : fresher) {
			if (m.sub.maps(p.first)) {
				fresher.erase(p.first);
			}
		}
		m.sub.compose(fresher, CompMode::SEMI);
		Subst sub;
		Subst outer;
		for (const auto& p : m.sub) {
			if (assertion_vars.count(p.first)) {
				outer.compose(LightSymbol(p.first, p.second.type), p.second.term);
			} else {
				sub.compose(LightSymbol(p.first, p.second.type), p.second.term);
			}
		}
		variants.emplace_back(make_unique<Prop>(m.data, std::move(sub), std::move(outer), std::move(fresher), this));
	}
	add_timer_stats("build_up_hyp_arrange_variants", timer);
	add_timer_stats("build_up_HYP", timer1);
}

bool Hyp::buildDown(set<Node*>& downs) {
	bool new_proofs = false;
	for (uint i = 0; i < parents.size(); ++ i) {
		Node* parent = parents.at(i);
		vector<ProofExpIndexed> news;
		for (uint i = 0; i < proofs.size(); ++i) {
			ProofExp* p = proofs[i].get();
			if (p->new_) {
				news.push_back({p, i});
			}
		}
		if (news.size()) {
			if (Prop* prop = dynamic_cast<Prop*>(parent)) {
				if (unify_down(prop, this, news)) {
					downs.insert(parent);
					new_proofs = true;
				}
			} else if (Ref* ref = dynamic_cast<Ref*>(parent)) {
				for (auto& p : news) {
					ProofRef* r = new ProofRef(*ref, p.proof, p.proof->hint);
					ref->proofs.emplace_back(r);
					downs.insert(ref);

					try {
						if (rus::Proof* rus_proof = r->proof()) {
							delete rus_proof;
						}
					} catch (Error& err) {
						cout << "FUCK 1)" << endl;
						cout << "THIS: " << endl << show() << endl;
						cout << "PARENT: " << endl << ref->show() << endl;
						cout << "proof: " << p.proof->show() << endl;
						/*cout << "CHILDREN: " << endl;
						for (const auto& v : variants) {
							cout << v->show() << endl;
						}*/

						throw err;
					}

					new_proofs = true;
				}
			} else {
				throw Error("impossibe: no Proof nor Ref");
			}
		}
	}
	return new_proofs;
}

bool Hyp::unifyWithGoalHyps(const rus::Hyp* hint) {
	bool ret = false;
	auto unified = space->hyps().unify(expr);
	for (const auto& m : unified) {
		if (hint) {
			proofs.push_back(make_unique<ProofTop>(*this, m.data, m.sub, m.data.get() == hint));
		} else {
			proofs.push_back(make_unique<ProofTop>(*this, m.data, m.sub, false));
			ret = true;
		}
	}
	return ret;
}

Prop::Prop(PropRef r, Subst&& s, Subst&& o, Subst&& f, Hyp* p) :
	Node(p), parent(p), prop(r), sub(std::move(s)), outer(std::move(o)), fresher(std::move(f)) {
	space->registerNode(this);
	if (isLeaf()) {
		proofs.push_back(make_unique<ProofProp>(*this, vector<ProofExp*>(), sub, hint));
	}
}

bool reacheable(const Node* parent, const Node* ancestor) {
	stack<const Node*> st;
	st.push(ancestor);
	while(!st.empty()) {
		const Node* n = st.top(); st.pop();
		if (n == parent) {
			return true;
		}
		if (const Prop* p = dynamic_cast<const Prop*>(n)) {
			st.push(p->parent);
		} else if (const Ref* r = dynamic_cast<const Ref*>(n)) {
			st.push(r->parent);
		} else if (const Hyp* h = dynamic_cast<const Hyp*>(n)) {
			for (const Node* p : h->parents) {
				st.push(p);
			}
		}
	}
	return false;
}

void Prop::buildUp() {
	Timer timer;
	bool vars = false;
	for (auto& h : prop.ass->hyps) {
		Term expr = outer.apply(sub.apply(fresher.apply(
			Tree2Term(*h->expr.tree(), ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX)
		)));
		auto variants = space->expressions().find(expr);
		Hyp* hyp = new Hyp(std::move(expr), this);
		if (variants.size() && !reacheable(variants.at(0).data, this)) {
			if (variants.size() > 1) {
				throw Error("variants size must be == 1");
			}
			hyp->variants.push_back(make_unique<Ref>(
				hyp,
				variants.at(0).data,
				space,
				std::move(variants.at(0).repl)
			));
			if (hint) {
				hyp->variants.back()->hint = true;
			}
			vars = true;
		}
		premises.emplace_back(hyp);
		if (hint) {
			premises.back()->hint = true;
		}
	}
	if (vars) {
		cout << "Prop::buildUp(): vars" << endl;
		cout << show_nodes_struct(this) << endl;
	}
	add_timer_stats("build_up_PROP", timer);
}

//#define VERIFY_UNIQUE_PROOFS

bool Prop::buildDown(set<Node*>& downs) {
	bool new_proofs = false;
	for (auto& p : proofs) {
		if (p->new_) {
			ProofHyp* hp =  new ProofHyp(*parent, p.get(), p->sub, p->hint);
#ifdef VERIFY_UNIQUE_PROOFS
			if (proofs.size() < 64) {
				// Don't check ALL proofs if there's too much (43050 for example)
				for (auto& h : parent->proofs) {
					if (hp->equal(h.get())) {
						cout << "DUPLICATE EXP PROOF" << endl;
						cout << hp->show() << endl;
						cout << "-----------" << endl;
						cout << h->show() << endl;
					}
				}
			}
#endif
			parent->proofs.emplace_back(hp);
			new_proofs = true;
		}
	}
	if (new_proofs) {
		downs.insert(parent);
	}
	return new_proofs;
}

}}}


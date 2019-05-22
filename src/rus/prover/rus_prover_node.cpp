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
				ret.compose(v.lit, Term(LightSymbol(w, ReplMode::KEEP_REPL, i)));
			}
		}
		assertion_vars.insert(v.lit);
	}
	return ret;
}

void Ref::buildUp() {
	// no need to grow up - already done
}

bool Ref::buildDown(set<Node*>& downs) {
	bool new_proofs = false;
	/*for (auto& p : proofs) {
		if (p->new_) {
			ProofExp* hp =  new ProofExp(*parent, p.get(), p->sub, p->hint);
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
	}*/
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
	Node(p), expr(p ? p->outer.apply(p->sub.apply(p->fresher.apply(e))) : std::move(e)) {
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
				outer.compose(p.first, p.second);
			} else {
				sub.compose(p.first, p.second);
			}
		}
		variants.emplace_back(make_unique<Prop>(m.data, std::move(sub), std::move(outer), std::move(fresher), this));
	}
	add_timer_stats("build_up_hyp_arrange_variants", timer);
	add_timer_stats("build_up_HYP", timer1);
}

bool Hyp::buildDown(set<Node*>& downs) {
	bool new_proofs;
	for (uint i = 0; i < parents.size(); ++ i) {
		Node* parent = parents.at(i);
		vector<ProofHypIndexed> news;
		for (uint i = 0; i < proofs.size(); ++i) {
			const ProofExp* p = proofs[i].get();
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
				if (unify_down(ref, this, news)) {
					downs.insert(parent);
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
	for (const auto& m : space->hyps().unify(expr)) {
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

void Prop::buildUp() {
	Timer timer;
	for (auto& h : prop.ass->hyps) {
		Term expr = Tree2Term(*h->expr.tree(), ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX);
		auto variants = space->expressions().varify(expr);
		Hyp* hyp = new Hyp(std::move(expr), this);
		if (variants.size()) {
			if (variants.size() > 1) {
				throw Error("variants size must be == 1");
			}
			hyp->variants.push_back(make_unique<Ref>(
				hyp,
				variants.at(0).data,
				space,
				std::move(variants.at(0).repl
			)));
			if (hint) {
				hyp->variants.back()->hint = true;
			}
		}
		premises.emplace_back(hyp);
		if (hint) {
			premises.back()->hint = true;
		}
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


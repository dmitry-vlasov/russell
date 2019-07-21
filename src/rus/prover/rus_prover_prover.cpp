#include "rus_prover_prover.hpp"

namespace mdl { namespace rus { namespace prover {

Prover::Prover(rus::Qed* q, Tactic* t) :
	Prover(q->step->proof()->theorem, q->prop, t) {
}

Prover::Prover(rus::Theorem* thm, rus::Prop* p, Tactic* t) : Space(t),
	theorem(thm),
	prop_(thm) {
	Timer timer;
	for (Assertion& ass : Sys::mod().math.get<Assertion>()) {
		if (!ass.token.preceeds(theorem->token)) {
			continue;
		}
		assertions_.add(
			Tree2Term(*ass.prop->expr.tree(), ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX),
			PropRef(&ass)
		);
	}
	for (uint i = 0; i < prop_.ass->arity(); ++ i) {
		HypRef hypRef(theorem, i);
		hyps_.add(Tree2Term(*hypRef.get()->expr.tree(), ReplMode::DENY_REPL), hypRef);
	}
	root_ = make_unique<Hyp>(Tree2Term(*prop_.get()->expr.tree(), ReplMode::DENY_REPL), this);
	buildUp(root_.get());
	add_timer_stats("space_init", timer);
}

void Prover::buildUp(Node* n) {
	if (Prop* p = dynamic_cast<Prop*>(n)) {
		buildUpProp(p);
	} else if (Hyp* h = dynamic_cast<Hyp*>(n)) {
		buildUpHyp(h);
	} else {
		throw Error("wrong node type for building up");
	}
}

void Prover::initProofs(Hyp* h, const rus::Hyp* hint) {
	if (Ref* ref = h->ref()) {
		for (const auto& p : ref->proofs) {

			cout << "REF PROOF EMPLACED: " << p->show() << endl;

			h->proofs.emplace_back(make_unique<ProofHyp>(*h, p.get(), p->sub, p->hint));
		}
	} else {
		auto unified = hyps_.unify(h->expr);
		for (const auto& m : unified) {
			if (hint) {
				h->proofs.emplace_back(make_unique<ProofTop>(*h, m.data->get(), m.sub, m.data->get() == hint));
			} else {
				h->proofs.emplace_back(make_unique<ProofTop>(*h, m.data->get(), m.sub, false));
			}
		}
	}
}

void Prover::buildUpProp(Prop* p) {
	Timer timer;
	bool vars = false;
	for (auto& h : p->prop.ass->hyps) {
		Hyp* hyp = new Hyp(
			p->outer.apply(p->sub.apply(p->fresher.apply(
				Tree2Term(*h->expr.tree(), ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX)
			))),
			p
		);
		p->premises.emplace_back(hyp);
		if (p->hint) {
			p->premises.back()->hint = true;
		}
	}
	add_timer_stats("build_up_PROP", timer);
}

static Subst make_free_vars_fresh(const Assertion* a, Space* space, set<uint>& assertion_vars, const Subst& s) {
	Subst ret;
	for (const auto& w : a->vars.v) {
		LightSymbol v(w, ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX);
		if (!ret.maps(v)) {
			if (!s.maps(v)) {
				ret.compose(v, space->freshVar(v));
			}
		}
		assertion_vars.insert(v.lit);
	}
	return ret;
}

static bool is_reacheable(const Node* parent, const Node* ancestor) {
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

void Prover::buildUpHyp(Hyp* h) {
	auto already_occured = expressions_.find(h->expr);
	// TODO: implement refs
	if (false && already_occured.size() && !is_reacheable(*already_occured.at(0).data, h)) {
		if (already_occured.size() > 1) {
			throw Error("already_occured size must be == 1");
		}
		h->variants.emplace_back(make_unique<Ref>(
			h,
			*already_occured.at(0).data,
			this,
			std::move(already_occured.at(0).repl)
		));
		if (h->hint) {
			h->variants.back()->hint = true;
		}
	} else {
		Timer timer1;
		Timer timer;
		auto unified = assertions_.unify(h->expr);
		add_timer_stats("build_up_hyp_unify_timer", timer);
		timer.start();
		for (auto& m : unified) {
			set<uint> assertion_vars;
			Subst fresher = make_free_vars_fresh(m.data->ass, this, assertion_vars, m.sub);
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
			h->variants.emplace_back(make_unique<Prop>(*m.data, std::move(sub), std::move(outer), std::move(fresher), h));
		}
		add_timer_stats("build_up_hyp_arrange_variants", timer);
		add_timer_stats("build_up_HYP", timer1);
	}
}

vector<unique_ptr<rus::Proof>> Prover::proved() {
	vector<unique_ptr<rus::Proof>> ret(Space::proved());
	for (auto& proof : ret) {
		rus::Step* st = proof->steps.back().get();
		proof->qed = make_unique<Qed>(prop_.get(), st);
		proof->theorem = theorem;
	}
	return ret;
}


}}}

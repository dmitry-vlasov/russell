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

Hyp::Hyp(const Term& e, Space* s) :
	Node(s), parent(nullptr), expr(e) {
	space->registerNode(this);
}

Hyp::Hyp(const Term& e, Prop* p) :
	Node(p), parent(p), expr(p ? p->outer.apply(p->sub.apply(p->fresher.apply(e))) : e) {
	space->registerNode(this);
}

Prop::Prop(const PropRef& r, const Subst& s, const Subst& o, const Subst& f, Hyp* p) :
	Node(p), parent(p), prop(r), sub(s), outer(o), fresher(f) {
	space->registerNode(this);
	if (isLeaf()) {
		proofs.push_back(make_unique<ProofProp>(*this, vector<ProofHyp*>(), sub, hint));
	}
}

void Prop::buildUp() {
	for (auto& h : prop.ass->hyps) {
		premises.push_back(make_unique<Hyp>(Tree2FlatTerm(*h->expr.tree(), ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX), this));
		if (hint) {
			premises.back()->hint = true;
		}
	}
}

void Hyp::buildUp() {
	for (auto& m : unify_general(space->assertions(), expr)) {
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
		variants.emplace_back(make_unique<Prop>(m.data, sub, outer, fresher, this));
	}
}

bool Hyp::unifyWithGoalHyps(const rus::Hyp* hint) {
	bool ret = false;
	for (const auto& m : unify_general(space->hyps(), expr)) {
		if (hint) {
			proofs.push_back(make_unique<ProofTop>(*this, m.data, m.sub, m.data.get() == hint));
		} else {
			proofs.push_back(make_unique<ProofTop>(*this, m.data, m.sub, false));
			ret = true;
		}
	}
	return ret;
}

//#define VERIFY_UNIQUE_PROOFS

bool Prop::buildDown(set<Node*>& downs) {
	bool new_proofs = false;
	for (auto& p : proofs) {
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
	}
	if (new_proofs) {
		downs.insert(parent);
	}
	return new_proofs;
}

bool Hyp::buildDown(set<Node*>& downs) {
	bool new_proofs = false;
	if (parent) {
		vector<ProofHypIndexed> news;
		for (uint i = 0; i < proofs.size(); ++i) {
			const ProofHyp* p = proofs[i].get();
			if (p->new_) {
				news.push_back({p, i});
			}
		}
		if (news.size()) {
			if (unify_down(parent, this, news)) {
				downs.insert(parent);
				new_proofs = true;
			}
		}
	}
	return new_proofs;
}

}}}


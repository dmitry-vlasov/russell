#include "rus_prover_tactics.hpp"
#include "rus_prover_maker.hpp"

namespace mdl { namespace rus { namespace prover {

static bool debug_make_tactic = true;

struct MakerTactic : public QueueTactic {
	MakerTactic(const AbstProof& aproof) : abst_proof_(aproof) {
		if (aproof.rootSize() == 1) {
			root = aproof.getRoot(0);
		} else {
			throw Error("ivalid proof tree - non a single root");
		}
	}
	void add(Prop* p) override {
		const Assertion* ass = p->prop.ass;
		if (debug_make_tactic) {
			cout << endl;
			cout << "make_tactic observing: " << show_id(ass->id()) << ", parent: " << p->parent->ind << endl;
		}
		auto proc_grand = [this, p, ass](Prop* grand_prop) {
			uint ind = 0;
			for (const auto& premise : grand_prop->premises) {
				if (p->parent == premise.get()) {
					break;
				}
				++ind;
			}
			if (propMap.count(grand_prop)) {
				const AbstProof::Node* n = propMap.at(grand_prop);
				const AbstProof::Node* candidate = n->getChild(ind);
				if (candidate && ass->id() == candidate->label()) {
					leafs.push_back(p);
					p->hint = true;
					if (debug_make_tactic) {
						cout << "make_tactic PUSHED: " << show_id(p->prop.id()) << ", index = " << p->ind << ", ref: " << ind << endl;
						cout << "this: " << (void*)p << ", parent: " << (void*)grand_prop << endl << endl;
						//cout << p->show() << endl << endl;
					}
					propMap[p] = candidate;
					observed.insert(candidate);
				}
			}
		};

		if (p->parent->root()) {
			if (ass->id() == root->label()) {
				leafs.push_back(p);
				p->hint = true;
				p->parent->hint = true;
				propMap[p] = root;
				observed.insert(root);
				if (debug_make_tactic) {
					cout << endl << "make_tactic PUSHED ROOT: " << show_id(p->prop.id()) << ", index = " << p->ind << endl;
					cout << "this: " << (void*)p << ", parent: " << (void*)root << endl << endl;
					//cout << p->show() << endl << endl;
				}
			}
		} else {
			for (Node* grand : p->parent->parents) {
				if (Prop* grand_prop = dynamic_cast<Prop*>(grand)) {
					proc_grand(grand_prop);
				} else if (Ref* grand_ref = dynamic_cast<Ref*>(grand)) {
					if (Prop* grand_prop = dynamic_cast<Prop*>(grand_ref->parent->parents[0])) {
						proc_grand(grand_prop);
					} else {
						throw Error("impossibe: grand of Ref MUST be Prop");
					}
				} else {
					throw Error("impossibe: no Proof nor Ref");
				}
			}
		}
	}

	const AbstProof::Node* mapProp(const Prop* p) const {
		auto it = propMap.find(p);
		if (it != propMap.end()) {
			return it->second;
		} else {
			return nullptr;
		}
	}
	vector<const AbstProof::Node*> mapHyp(const Hyp* h) const {
		vector<const AbstProof::Node*> ret;
		if (h->root()) {
			ret.push_back(root);
		} else {
			for (const Node* n : h->parents) {
				if (const Prop* p = dynamic_cast<const Prop*>(n)) {
					if (const AbstProof::Node* x = mapProp(p)) {
						ret.push_back(x);
					}
				}
			}
		}
		return ret;
	}

private:
	const AbstProof& abst_proof_;
	const AbstProof::Node* root;
	map<const Prop*, const AbstProof::Node*> propMap;
	set<const AbstProof::Node*> observed;
};

Maker::Maker(const AbstProof& aproof, uint id) :
	Space(new MakerTactic(aproof)), abst_proof_(aproof), theorem_id_(id) {
	theorem_ = make_unique<Theorem>(id);
	prop_.ass = theorem_.get();
	Timer timer;
	for (auto& p : Sys::mod().math.get<Assertion>()) {
		if (Assertion* ass = p.second.data) {
			/*if (!ass->token.preceeds(a->token)) {
				continue;
			}*/
			for (uint i = 0; i < ass->props.size(); ++i) {
				auto& prop = ass->props[i];
				assertions_.add(
					Tree2Term(*prop.get()->expr.tree(), ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX),
					PropRef(ass, i)
				);
			}
		} else {
			throw Error("undefined reference to assertion", Lex::toStr(p.first));
		}
	}
	if (abst_proof_.rootSize() != 1) {
		throw Error("ivalid proof tree - non a single root");
	}
	const Assertion* root_ass = Sys::mod().math.get<Assertion>().access(abst_proof_.getRoot(0)->label());
	root_ = make_unique<Hyp>(Tree2Term(*root_ass->props[0].get()->expr.tree(), ReplMode::KEEP_REPL), this);
	buildUp(root_.get());
	add_timer_stats("maker_init", timer);
}

/*inline uint find_index(const rus::Assertion* a, const rus::Prop* p) {
	uint c = 0;
	for (auto& x : a->props) if (x.get() == p) return c; else ++c;
	throw Error("prop is not found");
}*/
/*
Maker::Maker(rus::Assertion* a, rus::Prop* p, Tactic* t) : Space(t),
	prop_(a, find_index(a, p)) {
	Timer timer;
	for (auto& p : Sys::mod().math.get<Assertion>()) {
		if (Assertion* ass = p.second.data) {
			if (!ass->token.preceeds(a->token)) {
				continue;
			}
			for (uint i = 0; i < ass->props.size(); ++i) {
				auto& prop = ass->props[i];
				assertions_.add(
					Tree2Term(*prop.get()->expr.tree(), ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX),
					PropRef(ass, i)
				);
			}
		} else {
			throw Error("undefined reference to assertion", Lex::toStr(p.first));
		}
	}
	for (uint i = 0; i < prop_.ass->arity(); ++ i) {
		HypRef hypRef(a, i);
		hyps_.add(Tree2Term(*hypRef.get()->expr.tree(), ReplMode::DENY_REPL), hypRef);
	}
	root_ = make_unique<Hyp>(Tree2Term(*prop_.get()->expr.tree(), ReplMode::DENY_REPL), this);
	buildUp(root_.get());
	add_timer_stats("space_init", timer);
}*/

void Maker::buildUp(Node* n) {
	if (Prop* p = dynamic_cast<Prop*>(n)) {
		buildUpProp(p);
	} else if (Hyp* h = dynamic_cast<Hyp*>(n)) {
		buildUpHyp(h);
	} else {
		throw Error("wrong node type for building up");
	}
}

void Maker::initProofs(Hyp* h, const rus::Hyp* hint) {
	if (Ref* ref = dynamic_cast<Ref*>(h->variants.at(0).get())) {
		for (const auto& p : ref->proofs) {

			cout << "REF PROOF EMPLACED: " << p->show() << endl;

			h->proofs.emplace_back(make_unique<ProofHyp>(*h, p.get(), p->sub, p->hint));
		}
	} else {
		for (const auto& par : h->parents) {
			if (const Prop* p = dynamic_cast<const Prop*>(par)) {
				const AbstProof::Node* n = dynamic_cast<MakerTactic*>(tactic_.get())->mapProp(p);
				if (n->isLeaf() && hyps_.findExact(h->expr).size() == 0) {
					uint ind = theorem_->hyps.size();
					theorem_->hyps.emplace_back(make_unique<rus::Hyp>(ind, Term2Expr(h->expr)));
					hyps_.add(h->expr, HypRef(theorem_.get(), ind));
				}
			}
		}
		auto unified = hyps_.unify(h->expr);
		for (const auto& m : unified) {
			if (hint) {
				h->proofs.emplace_back(make_unique<ProofTop>(*h, m.data, m.sub, m.data.get() == hint));
			} else {
				h->proofs.emplace_back(make_unique<ProofTop>(*h, m.data, m.sub, false));
			}
		}
	}
}

const PropRef& Maker::prop(rus::Step* s) const {
	theorem_->props.emplace_back(make_unique<rus::Prop>(0, s->expr));
	return prop_;
}

void Maker::buildUpProp(Prop* p) {
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

void Maker::buildUpHyp(Hyp* h) {
	auto already_occured = expressions_.find(h->expr);
	// TODO: implement refs
	if (false && already_occured.size() && !is_reacheable(already_occured.at(0).data, h)) {
		if (already_occured.size() > 1) {
			throw Error("already_occured size must be == 1");
		}
		h->variants.emplace_back(make_unique<Ref>(
			h,
			already_occured.at(0).data,
			this,
			std::move(already_occured.at(0).repl)
		));
		if (h->hint) {
			h->variants.back()->hint = true;
		}
	} else {
		MakerTactic* t = dynamic_cast<MakerTactic*>(tactic_.get());
		set<uint> labels;
		for (auto c : t->mapHyp(h)) {
			labels.insert(c->label());
		}
		Timer timer1;
		Timer timer;
		auto unified = assertions_.unify(h->expr);
		add_timer_stats("build_up_hyp_unify_timer", timer);
		timer.start();
		for (auto& m : unified) {
			if (labels.find(m.data.ass->id()) == labels.end()) continue;
			set<uint> assertion_vars;
			Subst fresher = make_free_vars_fresh(m.data.ass, this, assertion_vars, m.sub);
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
			h->variants.emplace_back(make_unique<Prop>(m.data, std::move(sub), std::move(outer), std::move(fresher), h));
		}
		add_timer_stats("build_up_hyp_arrange_variants", timer);
		add_timer_stats("build_up_HYP", timer1);
	}
}

}}}


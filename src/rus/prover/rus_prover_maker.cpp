#include "rus_prover_tactics.hpp"
#include "rus_prover_maker.hpp"

namespace mdl { namespace rus { namespace prover {

static bool debug_make_tactic = true;

void all_nodes(const AbstProof::Node* n, set<const AbstProof::Node*>& all) {
	if (n) {
		all.insert(n);
		for (uint i = 0; i < n->childrenArity(); ++ i) {
			all_nodes(n->getChild(i), all);
		}
	}
}

inline uint find_index(const Prop* p, const Hyp* h) {
	uint c = 0;
	for (auto& x : p->premises) if (x.get() == h) return c; else ++c;
	throw Error("prop is not found");
}


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
						cout << "make_tactic PUSHED: " << show_id(p->prop.id()) << ", index = " << p->ind << ", ref: " << ind << ", ";
						//cout << "p: " << p->show() << endl;
						cout << "cand: " << candidate->show([](uint l) { return Lex::toStr(l); }) << endl;
						//cout << "this: " << (void*)p << ", parent: " << (void*)grand_prop << endl << endl;
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
					uint ind = find_index(p, h);
					if (const AbstProof::Node* x = mapProp(p)) {
						if (ind < x->childrenArity() && x->getChild(ind)) {
							ret.push_back(x->getChild(ind));
						}
					}
				}
			}
		}
		return ret;
	}
	string show() const override {
		set<const AbstProof::Node*> all;
		all_nodes(root, all);
		string ret;
		for (auto p : propMap) {
			all.erase(p.second);
		}
		ret += "MISSED STEPS:\n";
		for (auto p : all) {
			ret += Lex::toStr(p->label()) + "\n";
		}
		ret += "MISSED STEPS DONE\n\n";

		ret += "NODES:\n";
		for (auto p : propMap) {
			ret += "--------------------\n";
			ret += p.first->show(true);
			ret += p.first->parent->show(true);
			for (const auto& ch : p.first->premises) {
				ret += ch->show(true);
				if (ch->variants.size() == 1) {
					if (const Ref* r = dynamic_cast<const Ref*>(ch->variants[0].get())) {
						ret += r->show(true);
						ret += r->ancestor->show(true);
					}
				}
			}
			ret += "\n";
		}
		ret += "PROOFS DONE\n";
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
	if (Ref* ref = h->ref()) {
		for (const auto& p : ref->proofs) {

			cout << "REF PROOF EMPLACED: " << p->show() << endl;

			h->proofs.emplace_back(make_unique<ProofHyp>(*h, p.get(), p->sub, p->hint));
		}
	} else {
		vector<const AbstProof::Node*> children = dynamic_cast<MakerTactic*>(tactic_.get())->mapHyp(h);
		if (!children.size()) {
			cout << "LEAF : " << h->expr.show() << endl;
			vector<HypRef> refs = hyps_.findExact(h->expr);
			if (refs.size() == 0) {
				uint ind = theorem_->hyps.size();
				theorem_->hyps.emplace_back(make_unique<rus::Hyp>(ind, Term2Expr(h->expr)));
				HypRef ref(theorem_.get(), ind);
				hyps_.add(h->expr, ref);
				refs.push_back(ref);
				cout << "NEW LEAF : " << h->expr.show() << ", ind = " << ind << endl;
			}
			h->proofs.emplace_back(make_unique<ProofTop>(*h, refs.at(0), Subst(), true));
		} else {
			cout << "NON-LEAF : " << h->expr.show() << endl;
		}
		/*auto unified = hyps_.unify(h->expr);
		for (const auto& m : unified) {

			cout << "Unified with: " << m.data.ind << endl;
			cout << "subst: " << endl << m.sub << endl;

			if (hint) {
				h->proofs.emplace_back(make_unique<ProofTop>(*h, m.data, m.sub, m.data.get() == hint));
			} else {
				h->proofs.emplace_back(make_unique<ProofTop>(*h, m.data, m.sub, false));
			}
		}*/
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
		cout << "building up: " << h->ind << ", labels: {";
		for (auto c : t->mapHyp(h)) {
			if (c) {
				labels.insert(c->label());
				cout << Lex::toStr(c->label()) << " [" << c->show([](uint l) { return Lex::toStr(l); }) << "], ";
			}
		}
		cout << "}" << endl;

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
		cout << "building up finished" << endl;
		add_timer_stats("build_up_hyp_arrange_variants", timer);
		add_timer_stats("build_up_HYP", timer1);
	}
}

void Maker::expandUp(uint index, set<Node*>& leafs) {
	if (index >= nodes_.size()) {
		throw Error("OUT OF BOUNDARIES");
	}
	if (Prop* p = dynamic_cast<Prop*>(nodes_[index])) {
		if (p->isLeaf()) {
			leafs.insert(p);
		} else {
			if (p->mayGrowUp()) {
				buildUp(p);
				for (auto& h : p->premises) {
					Hyp* hyp = h.get();
					buildUp(hyp);
				}
				for (auto& h : p->premises) {
					if (h->isLeaf()) {
						leafs.insert(h.get());
					}
				}
			}
		}
	}
}

Return Maker::make() {
	set<Node*> leafs;
	cout << "BUILD TREE" << endl;
	while (Prop* p = tactic_->next()) {
		expandUp(p->ind, leafs);
	}
	cout << "INIT PROOF LEAFS" << endl;
	for (Node* n : leafs) {
		if (Hyp* h = dynamic_cast<Hyp*>(n)) {
			initProofs(h);
		}
	}
	cout << "COMPLETE DOWN" << endl;
	completeDown(leafs);
	return check_proved();
}


}}}


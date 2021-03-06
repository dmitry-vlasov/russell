#include "rus_prover_tactics.hpp"
#include "rus_prover_maker.hpp"

namespace mdl { namespace rus { namespace prover {

Subst make_free_vars_fresh(const Assertion* a, Space* space, set<uint>& assertion_vars, const Subst& s) {
	Subst ret;
	for (const auto& w : a->vars.v) {
		LightSymbol v = VarProvider::makeVar(w.lit(), w.type());
		if (!ret.maps(v)) {
			if (!s.maps(v)) {
				ret.compose(v, space->vars().makeFreshVar(w.lit(), w.type()));
			}
		}
		assertion_vars.insert(v.lit);
	}
	return ret;
}

Subst make_free_vars_fresh(const Assertion* a, Space* space) {
	Subst ret;
	for (const auto& w : a->vars.v) {
		LightSymbol v = VarProvider::makeVar(w.lit(), w.type());
		if (!ret.maps(v)) {
			ret.compose(v, space->vars().makeFreshVar(w.lit(), w.type()));
		}
	}
	return ret;
}

struct Maker : public Space {
	typedef vector<unique_ptr<rus::Proof>> Proved;
	template<class T>
	using IndexMap = unify::IndexMap<T>;

	Maker(const AbstProof& aproof, uint id);

	void registerNode(Node* n) {
		Space::registerNode(n);
		if (Hyp* h = dynamic_cast<Hyp*>(n)) {
			if (!expressions_.find(h->expr).size()) {
				expressions_.add(h->expr, h);
			}
		}
	}
	void unregisterNode(Node* n) {
		Space::unregisterNode(n);
		// TODO:
	}

	unique_ptr<Theorem> make();

	void buildUp(Node* n) override;
	void initProofs(Hyp* h, const rus::Hyp* hint = nullptr) override;

private:
	void expandUp(uint index, set<Node*>& leafs);

	void buildUpProp(Prop*);
	void buildUpHyp(Hyp*);

	uint theorem_id_;
	const AbstProof& abst_proof_;

	IndexMap<unique_ptr<rus::Hyp>> hyps_;
	IndexMap<PropRef>  assertions_;
	IndexMap<Hyp*>     expressions_;
};


unique_ptr<Theorem> make_theorem(const AbstProof& aproof, uint id) {
	Maker maker(aproof, id);
	return maker.make();
}

static bool debug_make_tactic = false;

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
	Timer timer;
	set<uint> visited;
	aproof.getRoot(0)->traverse([this, &visited](const AbstProof::Node& n) {
		if (!visited.count(n.label())) {
			visited.insert(n.label());
			if (Assertion* ass = Sys::mod().math.get<Assertion>().access(n.label())) {
				assertions_.add(
					Tree2Term(*ass->prop->expr.tree(), true),
					PropRef(ass)
				);
				//cout << "ADDED: " << Lex::toStr(n.label()) << endl;
			} else {
				throw Error("undefined reference to assertion", Lex::toStr(n.label()));
			}
		}
	});
	if (abst_proof_.rootSize() != 1) {
		throw Error("ivalid proof tree - non a single root");
	}
	//cout << "ASSSERTIONS: " << endl;
	//cout << assertions_.show() << endl;
	const Assertion* root_ass = Sys::mod().math.get<Assertion>().access(abst_proof_.getRoot(0)->label());
	Subst fresher = make_free_vars_fresh(root_ass, this);
	root_ = make_unique<Hyp>(
		fresher.apply(Tree2Term(*root_ass->prop->expr.tree(), true)), this
	);
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
			//cout << "LEAF : " << h->expr.show() << endl;
			vector<const unique_ptr<rus::Hyp>*> refs = hyps_.findExact(h->expr);
			if (refs.size() == 0) {
				hyps_.emplace(h->expr, make_unique<rus::Hyp>(hyps_.size(), std::move(Term2Expr(h->expr))));
				refs = hyps_.findExact(h->expr);
				//cout << "NEW LEAF : " << h->expr.show() << ", ind = " << (hyps_.size() - 1) << endl;
			}
			h->proofs.emplace_back(make_unique<ProofTop>(*h, refs.at(0)->get(), Subst(), true));
			//cout << "LEAF : " << h->expr.show() <<  " DANE " << endl;
		} else {
			//cout << "NON-LEAF : " << h->expr.show() << endl;
		}
	}
}

void Maker::buildUpProp(Prop* p) {
	Timer timer;
	bool vars = false;
	for (auto& h : p->prop.ass->hyps) {
		Hyp* hyp = new Hyp(
			p->outer.apply(p->sub.apply(p->fresher.apply(
				Tree2Term(*h->expr.tree(), true)
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
		MakerTactic* t = dynamic_cast<MakerTactic*>(tactic_.get());
		set<uint> labels;
		//cout << "building up: " << h->ind << ", labels: {";
		for (auto c : t->mapHyp(h)) {
			if (c) {
				labels.insert(c->label());
				//cout << Lex::toStr(c->label()) << " [" << c->show([](uint l) { return Lex::toStr(l); }) << "], ";
			}
		}
		//cout << "}" << endl;

		Timer timer1;
		Timer timer;
		auto unified = assertions_.unify(h->expr);
		add_timer_stats("build_up_hyp_unify_timer", timer);
		timer.start();
		for (auto& m : unified) {

			//cout << "unified: " << Lex::toStr(m.data->ass->id()) << endl;

			if (labels.find(m.data->ass->id()) == labels.end()) continue;
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

extern bool debug_gen_proof;
bool debug_maker = false;

unique_ptr<Theorem> Maker::make() {
	set<Node*> leafs;
	//cout << "BUILD TREE" << endl;
	while (Prop* p = tactic_->next()) {
		//cout << "expanding: " << p->ind << endl;
		expandUp(p->ind, leafs);
	}
	//cout << "INIT PROOF LEAFS" << endl;
	for (Node* n : leafs) {
		if (Hyp* h = dynamic_cast<Hyp*>(n)) {
			initProofs(h);
		}
	}
	//cout << "COMPLETE DOWN" << endl;
	completeDown(leafs);

	if (debug_maker) {
		cout << show_nodes_struct(root()) << endl;
	}

	if (root_->proofs.size() > 0) {
		ProofNode* root = root_->proofs.at(0)->clone();
		vector<unique_ptr<ProofNode>> detached;
		vector<unique_ptr<rus::Hyp>> leafs;

		traverseProof(root, [&detached, &leafs](ProofNode* n) {
			detached.emplace_back(n);
			if (ProofTop* t = dynamic_cast<ProofTop*>(n)) {
				t->hyp = new rus::Hyp(*t->hyp);
				leafs.emplace_back(t->hyp);
			}
		});
		map<rus::Hyp*, rus::Hyp*> map_hyp2ret;

		//cout << "DETACHED " << Lex::toStr(theorem_id_) << endl;
		auto generated_proof = gen_proof(root);
		if (generated_proof) {
			unique_ptr<Theorem> ret = make_unique<Theorem>(theorem_id_);
			generated_proof->theorem = ret.get();
			ret->proof = std::move(generated_proof);
			traverseProof(root, [&ret, &map_hyp2ret](ProofNode* n) {
				if (ProofTop* t = dynamic_cast<ProofTop*>(n)) {
					bool found = false;
					for (auto& h : ret->hyps) {
						if (h->expr == t->hyp->expr) {
							map_hyp2ret[t->hyp] = h.get();
							found = true;
							break;
						}
					}
					if (!found) {
						ret->hyps.emplace_back(make_unique<rus::Hyp>(*t->hyp));
						ret->hyps.back()->ind = ret->hyps.size() - 1;
						map_hyp2ret[t->hyp] = ret->hyps.back().get();
					}
				}
			});
			rus::Step* step = ret->proof->steps.back().get();
			ret->prop = make_unique<rus::Prop>(step->expr);
			rus::traverseProof(ret->proof->qed(), [&map_hyp2ret](Writable* n) {
				if (rus::Step* s = dynamic_cast<rus::Step*>(n)) {
					for (auto& r : s->refs) {
						if (rus::Hyp* h = r->hyp()) {
							r.reset(new rus::Ref(map_hyp2ret.at(h)));
						}
					}
				}
			});
			std::sort(ret->hyps.begin(), ret->hyps.end(), [](auto& h1, auto& h2) { return h1->ind < h2->ind; });
			complete_assertion_vars(ret.get());
			complete_proof_vars(ret->proof.get());
			try {
				ret->verify(VERIFY_SRC);
				return ret;
			} catch (Error& err) {
				err.msg += "at maker\n";
				throw err;
			}
		} else {
			cout << "gen_proof failed: " << Lex::toStr(theorem_id_) << endl;
			return nullptr;
		}
	} else {
		cout << "root_->proofs.size() == 0: " << Lex::toStr(theorem_id_) << endl;
		cout << show_nodes_struct(root_.get()) << endl;
		return nullptr;
	}
}

}}}

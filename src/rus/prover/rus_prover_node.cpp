#include "rus_prover_space.hpp"
#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

Node::~Node() {
	space->unregisterNode(this);
}

static Subst make_free_vars_fresh(const Assertion* a, map<uint, uint>& vars, set<uint>& assertion_vars, const Subst& s) {
	Subst ret;
	for (const auto& w : a->vars.v) {
		LightSymbol v(w, ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX);
		if (!ret.maps(v)) {
			if (!s.maps(v)) {
				uint i = vars.count(v.lit) ? vars[v.lit] + 1 : LightSymbol::INTERNAL_MIN_INDEX;
				vars[v.lit] = i;
				ret.compose(v.lit, Term(LightSymbol(w, ReplMode::KEEP_REPL, i)));
			}
		}
		assertion_vars.insert(v.lit);
	}
	return ret;
}

Hyp::Hyp(const Term& e, Space* s) :
	Node(s), parent(nullptr), expr(e) {
	if (parent && parent->autoGoDown) {
		unifyWithGoalHyps();
	}
	space->registerNode(this);
}

Hyp::Hyp(const Term& e, Prop* p) :
	Node(p), parent(p), expr(p ? apply(p->outer, apply(p->sub, apply(p->fresher, e))) : e) {
	space->registerNode(this);
}

Prop::Prop(const PropRef& r, const Subst& s, const Subst& o, const Subst& f, Hyp* p) :
	Node(p), parent(p), prop(r), sub(s), outer(o), fresher(f) {
	space->registerNode(this);
	if (isLeaf()) {
		proofs.emplace_back(new ProofProp(*this, vector<ProofHyp*>(), sub));
	}
}

void Prop::buildUp() {
	for (auto& h : prop.ass->hyps) {
		Hyp* hyp = new Hyp(Tree2FlatTerm(*h->expr.tree(), ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX), this);
		premises.emplace_back(hyp);
	}
}

void Hyp::buildUp() {
	for (auto& m : unify_general(space->assertions_, expr)) {
		set<uint> assertion_vars;
		Subst fresher = make_free_vars_fresh(m.data.ass, space->vars, assertion_vars, m.sub);
		for (const auto& p : fresher) {
			if (m.sub.maps(p.first)) {
				fresher.erase(p.first);
			}
		}
		m.sub.compose(fresher, false);
		Subst sub;
		Subst outer;
		for (const auto& p : m.sub) {
			if (assertion_vars.count(p.first)  /*p.first.ind == LightSymbol::ASSERTION_INDEX*/) {
				outer.compose(p.first, p.second);
			} else {
				sub.compose(p.first, p.second);
			}
		}
		Prop* prop = new Prop(m.data, sub, outer, fresher, this);
		variants.emplace_back(prop);
	}
}

bool Hyp::unifyWithGoalHyps(const rus::Hyp* hint) {
	bool show_this = false; //(47 <= ind && ind <= 49);

	if (show_this) {
		cout << "HYP UNIFYING " << ind << " EXPR: " << expr.show() << endl;
	}
	bool ret = false;
	for (const auto& m : unify_general(space->hyps_, expr)) {
		if (hint) {
			if (m.data.get() == hint) {
				ProofTop* pt = new ProofTop(*this, m.data, m.sub);
				if (show_this) {
					cout << "\tUNIFIED WITH TOP: " << pt->expr.show() << endl;
					cout << "\tIND: " << pt->ind << endl;
					cout << "\tSUB:" << endl;
					cout << Indent::paragraph(pt->sub.show()) << endl;
				}

				proofs.emplace_back(pt);
				ret = true;
			}
		} else {
			ProofTop* pt = new ProofTop(*this, m.data, m.sub);
			if (show_this) {
				cout << "\tUNIFIED WITH TOP: " << pt->expr.show() << endl;
				cout << "\tIND: " << pt->ind << endl;
				cout << "\tSUB:" << endl;
				cout << Indent::paragraph(pt->sub.show()) << endl;
			}

			proofs.emplace_back(pt);
			ret = true;
		}
	}
	return ret;
	//cout << endl;

	/*
	//cout << "COMPLETING: " << ind << endl;
	static  uint c = 0;
	set<Node*> downs;
	downs.insert(this);
	while (!downs.empty()) {
		Node* n = *downs.begin();
		//cout << "DOWNING: " << n->ind << ", c = " << c++ << endl;
		downs.erase(n);
		auto n_downs = n->buildDown();
		for (auto x : n_downs) {
			downs.insert(x);
		}
	}*/
}

bool Prop::buildDown(set<Node*>& downs) {
	bool new_proofs = false;
	for (auto& p : proofs) {
		if (p->new_) {
			//cout << "HYP: " << parent->ind << " - " << p.get()->show() << endl;
			//cout << "PROP: " << ind << endl;
			//cout << "BUILDING DOWN HYP: " << parent->ind << endl;
			ProofExp* hp =  new ProofExp(*parent, p.get(), p->sub);
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
			parent->proofs.emplace_back(hp);
			new_proofs = true;
		} else {
			//cout << "OLD PROP: " << p->node.ind << endl;
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


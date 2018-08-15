#include "rus_prover_space.hpp"
#include "rus_prover_unify.hpp"
#include "rus_prover_decart.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_unify_subs = false;
bool debug_unify_subs_1 = false;

Node::~Node() {
	space->unregisterNode(this);
}

static Subst make_free_vars_fresh(const Assertion* a, map<uint, uint>& vars, Subst& s) {
	Subst ret;
	for (const auto& w : a->vars.v) {
		LightSymbol v(w, ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX);
		if (!ret.maps(v)) {
			if (!s.maps(v)) {
				uint i = vars.count(v.lit) ? vars[v.lit] + 1 : LightSymbol::INTERNAL_MIN_INDEX;
				vars[v.lit] = i;
				ret.sub[v] = LightTree(LightSymbol(w, ReplMode::KEEP_REPL, i));
			}
		}
	}
	return ret;
}

Hyp::Hyp(const LightTree& e, Space* s) :
	Node(s), parent(nullptr), expr(e) {
	complete();
	space->registerNode(this);
}

Hyp::Hyp(const LightTree& e, Prop* p) :
	Node(p), parent(p), expr(p ? apply(p->outer, apply(p->sub, apply(p->fresher, e))) : e) {
	space->registerNode(this);
}

Prop::Prop(const PropRef& r, const Subst& s, const Subst& o, const Subst& f, Hyp* p) :
	Node(p), parent(p), prop(r), sub(s), outer(o), fresher(f) {
	//Subst fresher = make_free_vars_fresh(r.ass, sub, space->vars);

	//cout << "ASS: " << Lex::toStr(r.id()) << endl;
	//cout << "FRESHER: " << endl;
	//cout << prover::show(fresher) << endl;

	space->registerNode(this);
}

void Prop::buildUp() {
	for (auto& h : prop.ass->hyps) {
		//cout << "ASS HYP: " << rus::show(h->expr) << endl;
		//cout << "SUB: " << prover::show(sub) << endl;
		//cout << "NODE EXPR: " << prover::show(apply(sub, convert_tree(*h->expr.tree()))) << endl;

		Hyp* hyp = new Hyp(convert_tree(*h->expr.tree(), ReplMode::KEEP_REPL, LightSymbol::ASSERTION_INDEX), this);
		//cout << "HYP EXPR: " << prover::show(hyp->expr) << endl;

		premises.emplace_back(hyp);
	}
}

void Hyp::buildUp() {

	for (auto& m : space->assertions.unify(expr)) {

		bool show_this = false; //(ind == 14) /*&& (Lex::toStr(m.data.id()) == "ax-3")*/;

		Subst fresher = make_free_vars_fresh(m.data.ass, space->vars, m.sub);
		if (show_this) {
			cout << "=========================" << endl;
			cout << "HYP THIS: " << prover::show(expr) << endl;
			cout << "PROP UP: " << Lex::toStr(m.data.id()) << endl;
			cout << "SUB:" << endl << prover::show(m.sub) << endl;
			cout << "FRESHER:" << endl << prover::show(fresher) << endl;
		}


		for (const auto& p : fresher.sub) {
			if (m.sub.sub.count(p.first)) {
				fresher.sub.erase(p.first);
			}
		}
		compose(m.sub, fresher, false);

		Subst sub;
		Subst outer;
		for (const auto& p : m.sub.sub) {
			if (p.first.ind == LightSymbol::ASSERTION_INDEX) {
				outer.sub[p.first] = p.second;
			} else {
				sub.sub[p.first] = p.second;
			}
		}

		if (show_this) {
			cout << "--------------------------" << endl;
			cout << "SUB:" << endl << prover::show(m.sub) << endl;
			cout << "FRESHER:" << endl << prover::show(fresher) << endl << endl << endl;
		}

		Prop* prop = new Prop(m.data, sub, outer, fresher, this);
		variants.emplace_back(prop);
		if (!prop->prop.ass->arity()) {
			ProofProp* pp = new ProofProp(*prop, {}, sub);
			prop->proofs.emplace_back(pp);
			proofs.emplace_back(new ProofExp(*this, pp, sub));

			if (show_this) {
				cout <<  "AX MET: " << prop->ind << " -- " << prop->proofs.size() << endl;
				cout <<  "EXPR: " << prover::show(apply(m.sub, expr)) << endl;
				cout <<  "SUB: " << endl;
				cout <<  Indent::paragraph(prover::show(m.sub)) << endl;
			}
		}
	}
}

void Hyp::complete() {
	bool show_this = false; //(47 <= ind && ind <= 49);

	if (show_this) {
		cout << "HYP UNIFYING " << ind << " EXPR: " << prover::show(expr) << endl;
	}


	for (const auto& m : space->hyps.unify(expr)) {
		ProofTop* pt = new ProofTop(*this, m.data, m.sub);
		if (show_this) {
			cout << "\tUNIFIED WITH TOP: " << prover::show(pt->expr) << endl;
			cout << "\tIND: " << pt->ind << endl;
			cout << "\tSUB:" << endl;
			cout << Indent::paragraph(prover::show(pt->sub)) << endl;
		}

		proofs.emplace_back(pt);
	}
	//cout << endl;

	//cout << "COMPLETING: " << ind << endl;
	set<Node*> downs;
	downs.insert(this);
	while (!downs.empty()) {
		Node* n = *downs.begin();
		//cout << "DOWNING: " << n->ind << endl;
		downs.erase(n);
		for (auto x : n->buildDown()) {
			downs.insert(x);
		}
	}
}

struct MultyTree {
	MultyTree(const Subst& s1, const Subst& s2) {
		add(s1);
		add(s2);
	}
	MultyTree(const vector<ProofHyp*>& ch) {
		for (auto p : ch) {
			add(p->sub);
		}
	}
	Subst makeSubs(Subst& unif) const {
		Subst ret;
		for (const auto& p : msub_) {
			ret.sub[p.first] = unify(p.second, unif);
			if (ret.sub[p.first].empty()) {
				ret.ok = false;
				break;
			}
		}
		return ret;
	}

private:
	void add(const Subst& s) {
		for (const auto& p : s.sub) {
			msub_[p.first].push_back(p.second);
		}
	}
	map<LightSymbol, vector<LightTree>> msub_;
};

Subst unify_subs(const MultyTree& t) {
	Subst unif;
	Subst gen;
	gen = t.makeSubs(unif);
	if (!(gen.ok && unif.ok)) {
		return Subst(false);
	}
	if (!unif.intersects(gen)) {
		if (unif.compose(gen)) {
			return unif;
		} else {
			return Subst(false);
		}
	} else {
		MultyTree t1(unif, gen);
		return unify_subs(t1);
	}
}

vector<Node*> unify_subs(Prop* pr, ProofHyp* h) {
	vector<ProofHyp*> proofs;
	DecartIter ind;
	for (auto& x : pr->premises) {
		if (x.get() != &h->node) {
			ind.addDim(x->proofs.size());
		} else {
			ind.addFixed(find_in_vector(x->proofs, h));
		}
	}
	if (ind.empty()) {
		return vector<Node*>();
	}

	debug_unify_subs = false; //(/*pr->space->ind == 5 &&*/ pr->ind == 21);

	if (debug_unify_subs) {
		cout << endl << "IND: " << ind.show() << endl << endl;
	}
	bool new_proofs = false;

	while (true) {
		vector<ProofHyp*> ch;
		if (debug_unify_subs) {
			cout << "CURRENT: " << ind.current() << endl;
			cout << "UNIFYING: \n--------------" << endl;
			cout << "PROP: " << pr->ind << endl;
		}
		for (uint i = 0; i < ind.size(); ++ i) {
			ProofHyp* ph = pr->premises[i].get()->proofs[ind[i]].get();
			if (debug_unify_subs) {
				cout << ph->ind << ": " << show(ph->expr) << endl;
				cout << "sub:" << endl;
				cout << Indent::paragraph(show(ph->sub)) << endl;
			}
			ch.push_back(ph);
		}
		if (debug_unify_subs) {
			cout << "-------------" << endl;
		}
		MultyTree t(ch);
		Subst sub = unify_subs(t);
		uint watchdog = 0;
		while (sub.composeable(sub)) {
			if (watchdog++ > 32) {
				cout << "SOMETHING WRONG" << endl;
				break;
			}
			if (!sub.compose(sub)) {
				sub.ok = false;
				break;
			}
		}
		if (sub.ok) {
			Subst delta = pr->sub;
			delta.compose(sub);
			ProofProp* pp = new ProofProp(*pr, ch, delta);
			for (auto& h : pr->proofs) {
				if (pp->equal(h.get())) {
					cout << "DUPLICATE PROP PROOF" << endl;
					cout << pp->show() << endl;
					cout << "-----------" << endl;
					cout << h->show() << endl;
				}
			}
			pr->proofs.emplace_back(pp);
			if (debug_unify_subs) {
				cout << "OK:\n" << show(sub) << endl;
			}
			new_proofs = true;
		} else {
			if (debug_unify_subs) {
				cout << "FAIL" << endl;
			}
		}
		if (debug_unify_subs) {
			cout << endl << endl << endl;
		}
		if (!ind.hasNext()) {
			break;
		}
		ind.makeNext();
	}
	if (new_proofs) {
		return {pr};
	} else {
		return vector<Node*>();
	}
}

vector<Node*> Prop::buildDown() {
	bool new_proofs = false;
	for (auto& p : proofs) {
		if (p->new_) {
			//cout << "HYP: " << parent->ind << " - " << p.get()->show() << endl;
			//cout << "PROP: " << ind << endl;
			//cout << "BUILDING DOWN HYP: " << parent->ind << endl;
			ProofExp* hp =  new ProofExp(*parent, p.get(), p->sub);
			for (auto& h : parent->proofs) {
				if (hp->equal(h.get())) {
					cout << "DUPLICATE EXP PROOF" << endl;
					cout << hp->show() << endl;
					cout << "-----------" << endl;
					cout << h->show() << endl;
				}
			}
			parent->proofs.emplace_back(hp);
			new_proofs = true;
		} else {
			//cout << "OLD PROP: " << p->node.ind << endl;
		}
	}
	if (new_proofs) {
		return {parent};
	} else {
		return vector<Node*>();
	}
}

vector<Node*> Hyp::buildDown() {
	vector<Node*> ret;
	if (parent) {
		for (auto& p : proofs) {
			if (p->new_) {
				//cout << "BUILDING DOWN PROP: " << p->node.ind << endl;
				for (auto& q : unify_subs(parent, p.get())) {
					ret.push_back(q);
				}
			} else {
				//cout << "OLD HYP: " << p->node.ind << endl;
			}
		}
	}
	return ret;
}

}}}


#include "rus_prover_down.hpp"

#include "rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_unify_subs = false;
bool debug_unify_subs_1 = false;

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

Subst unify_subs_1(Subst unif, Subst gen);

Subst unify_subs_1(const MultyTree& t) {
	Subst unif;
	return unify_subs_1(t.makeSubs(unif), unif);
}

Subst unify_subs_1(Subst unif, Subst gen) {
	if (!(gen.ok && unif.ok)) {
		return Subst(false);
	}
	if (!unif.intersects(gen)) {
		if (unif.compose(gen)) {
			uint watchdog = 0;
			while (unif.composeable(unif)) {
				if (watchdog++ > 32) {
					cout << "SOMETHING WRONG" << endl;
					break;
				}
				if (!unif.compose(unif)) {
					unif.ok = false;
					break;
				}
			}
			return unif;
		} else {
			return Subst(false);
		}
	} else {
		MultyTree t1(unif, gen);
		return unify_subs_1(t1);
	}
}

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

vector<Node*> unify_down(Prop* pr, const ProofHyp* h) {
	CartesianIter ind;
	for (auto& x : pr->premises) {
		if (x.get() != &h->node) {
			ind.addDim(x->proofs.size());
		} else {
			ind.addFixed(x->proofs.size(), find_in_vector(x->proofs, h));
		}
	}
	if (ind.card() == 0) {
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

}}}


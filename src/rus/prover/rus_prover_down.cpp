#include "rus_prover_down.hpp"

#include "rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover {

bool debug_unify_subs = false;
bool debug_unify_subs_1 = false;

struct MultySubst {
	MultySubst(const vector<const Subst*>& subs) {
		for (auto s : subs) {
			add(s);
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
	void add(const Subst* s) {
		for (const auto& p : s->sub) {
			msub_[p.first].push_back(p.second);
		}
	}
	map<LightSymbol, vector<LightTree>> msub_;
};


void sub_closure(Subst& sub) {
	enum { WATCHDOG_THRESHOLD = 32 };
	uint watchdog = 0;
	while (sub.composeable(sub)) {
		if (watchdog++ > WATCHDOG_THRESHOLD) {
			cout << "SOMETHING WRONG: too much deep substitution closure" << endl;
			break;
		}
		if (!sub.compose(sub)) {
			sub.ok = false;
			break;
		}
	}
}

Subst unify_subs(Subst unif, Subst gen);

Subst unify_subs(const MultySubst& t) {
	Subst unif;
	return unify_subs(unif, t.makeSubs(unif));
}

Subst unify_subs(Subst unif, Subst gen) {
	if (!(gen.ok && unif.ok)) {
		return Subst(false);
	}
	if (!unif.intersects(gen)) {
		if (unif.compose(gen)) {
			sub_closure(unif);
			return unif;
		} else {
			return Subst(false);
		}
	} else {
		MultySubst msub({&unif, &gen});
		return unify_subs(msub);
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
		vector<const Subst*> subs;
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
			subs.push_back(&ph->sub);
		}
		if (debug_unify_subs) {
			cout << "-------------" << endl;
		}
		Subst sub = unify_subs(MultySubst(subs));
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


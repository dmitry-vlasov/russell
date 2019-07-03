#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

Node::~Node() {
	space->unregisterNode(this);
}

// Ref -------------------------

Ref::Ref(Hyp* p, Hyp* a, Space* s, VarRepl&& r) :
	Node(s), parent(p), ancestor(a), repl(std::move(r)) {
	space->registerNode(this);
	ancestor->parents.push_back(this);
	cout << "Ref  " << ind << " is built, parent: " << p->ind << " = " << p->expr << ", child: " << a->ind << " = " << a->expr << endl;
	cout << "var repl:" << endl;
	cout << repl.show() << endl;
	for (auto& p : ancestor->proofs) {
		proofs.emplace_back(make_unique<ProofRef>(*this, p.get(), p->hint));
	}
}

bool Ref::buildDown(set<Node*>& downs) {
	bool new_proofs = false;
	for (const auto& p : proofs) {
		if (p->new_) {
			ProofHyp* parent_proof = new ProofHyp(*parent, p.get(), p->sub, p->hint);
#ifdef VERIFY_UNIQUE_PROOFS
			if (parent->proofs.size() < 64) {
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
			parent->proofs.emplace_back(parent_proof);

			try {
				if (rus::Proof* rus_proof = parent_proof->proof()) {
					delete rus_proof;
				}
			} catch (Error& err) {
				cout << "FUCK 2)" << endl;
				cout << "THIS: " << endl << show() << endl;
				//cout << "PARENT: " << endl << ref->show() << endl;
				//cout << "proof: " << p.proof->show() << endl;
				throw err;
			}

			new_proofs = true;
		}
	}
	if (new_proofs) {
		downs.insert(parent);
	}
	return new_proofs;
}



// Hyp -------------------------

Hyp::Hyp(Term&& e, Space* s) :
	Node(s), expr(std::move(e)) {
	space->registerNode(this);
}

Hyp::Hyp(Term&& e, Prop* p) :
	Node(p), expr(std::move(e)) {
	parents.push_back(p);
	space->registerNode(this);
}

bool Hyp::buildDown(set<Node*>& downs) {
	bool new_proofs = false;
	for (uint i = 0; i < parents.size(); ++ i) {
		Node* parent = parents.at(i);
		vector<ProofExpIndexed> news;
		for (uint i = 0; i < proofs.size(); ++i) {
			ProofExp* p = proofs[i].get();
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
				for (auto& p : news) {
					ProofRef* r = new ProofRef(*ref, p.proof, p.proof->hint);
					ref->proofs.emplace_back(r);
					downs.insert(ref);

					try {
						if (rus::Proof* rus_proof = r->proof()) {
							delete rus_proof;
						}
					} catch (Error& err) {
						cout << "FUCK 1)" << endl;
						cout << "THIS: " << endl << show() << endl;
						cout << "PARENT: " << endl << ref->show() << endl;
						cout << "proof: " << p.proof->show() << endl;
						/*cout << "CHILDREN: " << endl;
						for (const auto& v : variants) {
							cout << v->show() << endl;
						}*/

						throw err;
					}

					new_proofs = true;
				}
			} else {
				throw Error("impossibe: no Proof nor Ref");
			}
		}
	}
	return new_proofs;
}






// Prop -------------------------

Prop::Prop(PropRef r, Subst&& s, Subst&& o, Subst&& f, Hyp* p) :
	Node(p), parent(p), prop(r), sub(std::move(s)), outer(std::move(o)), fresher(std::move(f)) {
	space->registerNode(this);
	if (isLeaf()) {
		proofs.push_back(make_unique<ProofProp>(*this, vector<ProofExp*>(), sub, hint));
	}
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


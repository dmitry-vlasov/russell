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
	for (const auto& v : a->vars.v) {
		if (!ret.maps(v.lit)) {
			if (!s.maps(v.lit)) {
				uint n = vars.count(v.lit) ? vars[v.lit] + 1 : 0;
				vars[v.lit] = n;
				LightSymbol s(v);
				s.lit = Lex::toInt(Lex::toStr(v.lit) + "_" + to_string(n));
				ret.sub[v.lit] = LightTree(s);
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
	Node(p), parent(p), expr(p ? apply(p->sub, apply(p->fresher, e)) : e) {
	space->registerNode(this);
}

Prop::Prop(const PropRef& r, const Subst& s, const Subst& f, Hyp* p) :
	Node(p), parent(p), prop(r), sub(s), fresher(f) {
	//Subst fresher = make_free_vars_fresh(r.ass, sub, space->vars);

	//cout << "ASS: " << Lex::toStr(r.id()) << endl;
	//cout << "FRESHER: " << endl;
	//cout << prover::show(fresher) << endl;

	/*for (const auto& p : fresher.sub) {
		sub.sub.erase(p.first);
	}
	compose(sub, fresher, false);*/
	space->registerNode(this);
}

void Prop::buildUp() {
	for (auto& h : prop.ass->hyps) {
		//cout << "ASS HYP: " << rus::show(h->expr) << endl;
		//cout << "SUB: " << prover::show(sub) << endl;
		//cout << "NODE EXPR: " << prover::show(apply(sub, convert_tree(*h->expr.tree()))) << endl;

		Hyp* hyp = new Hyp(convert_tree(*h->expr.tree()), this);
		//cout << "HYP EXPR: " << prover::show(hyp->expr) << endl;

		premises.emplace_back(hyp);
	}
	/*for (auto& p : premises) {
		p.get()->complete();
	}*/
}

void Hyp::buildUp() {
	/*static int c = 0;
	++c;
	cout << endl << "MATCHING: " << prover::show(expr) << endl;
	for (const auto& p : space->assertions.match_forth(expr)) {
		//cout << "PROP EXPR: " << rus::show(p.first.ass->props[0]->expr) << endl;
		//cout << "SUB: " << prover::show(p.second) << endl;
		if (apply(p.second.sub, convert_tree(*p.second.data.ass->props[0]->expr.tree())) != expr) {
			cout << "MATCHING FAILED: " << prover::show(apply(p.second.sub, convert_tree(*p.second.data.ass->props[0]->expr.tree()))) << endl;
		}

		cout << "ASS: " << Lex::toStr(p.second.data.id()) << endl;
		Prop* prop = new Prop(p.second.data, p.second.sub, this);
		variants.emplace_back(prop);
		if (!prop->prop.ass->arity()) {
			ProofProp* pr = new ProofProp(*prop);
			prop->proofs.emplace_back(pr);
			proofs.emplace_back(new ProofExp(*this, pr, p.second.sub));
			//cout <<  "AX MET: " << prop->ind << " -- " << prop->proofs.size() << endl;
		}
	}*/


	for (auto& m : space->assertions.unify(expr)) {

		bool show_this = (ind == 4) && (Lex::toStr(m.data.id()) == "ax-3");

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
				/*const LightTree& ex = m.sub.sub[p.first];
				if (!(ex.kind() == LightTree::VAR && !ex.var().rep)) {
					//cout << "ERASING: " << Lex::toStr(p.first) << " --> " << prover::show(m.sub.sub[p.first]) << endl;
					//m.sub.sub.erase(p.first);
				} else {
					fresher.sub.erase(p.first);
				}*/
				fresher.sub.erase(p.first);
			}
		}
		compose(m.sub, fresher, false);

		if (show_this) {
			cout << "--------------------------" << endl;
			cout << "SUB:" << endl << prover::show(m.sub) << endl;
			cout << "FRESHER:" << endl << prover::show(fresher) << endl << endl << endl;
		}

		Prop* prop = new Prop(m.data, m.sub, fresher, this);
		variants.emplace_back(prop);
		if (!prop->prop.ass->arity()) {
			ProofProp* pp = new ProofProp(*prop, {}, m.sub);
			prop->proofs.emplace_back(pp);
			proofs.emplace_back(new ProofExp(*this, pp, m.sub));

			//cout <<  "AX MET: " << prop->ind << " -- " << prop->proofs.size() << endl;
			//cout <<  "EXPR: " << prover::show(apply(m.sub, expr)) << endl;
			//cout <<  "SUB: " << endl;
			//cout <<  Indent::paragraph(prover::show(m.sub)) << endl;
		}
	}
}

void Hyp::complete() {
	for (const auto& m : space->hyps.unify(expr)) {
		proofs.emplace_back(new ProofTop(*this, m.data, m.sub));
	}
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

struct MultySub {
	MultySub() : ok(true) { }
	map<uint, Unified> msub_;
	bool ok;
};

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
	MultySub makeSubs() const {
		MultySub ret;
		for (const auto& p : msub_) {
			Unified s = unify(p.second);
			if (s.sub.ok) {
				ret.msub_[p.first] = std::move(s);
			} else {
				ret.ok = false;
				break;
			}
		}
		return ret;
	}

private:
	void add(const Subst& s) {
		for (const auto& p : s.sub)
			msub_[p.first].push_back(&p.second);
	}
	map<uint, vector<const LightTree*>> msub_;
};

inline bool intersects(const Subst& s1, const Subst& s2) {
	for (const auto& p : s1.sub) {
		if (s2.sub.count(p.first)) return true;
	}
	return false;
}

Subst unify_subs(const MultyTree& t) {
	MultySub m = t.makeSubs();
	if (!m.ok) {
		return Subst(false);
	}
	Subst com;
	Subst gen;
	for (auto& p : m.msub_) {
		if (!com.compose(p.second.sub)) {
			return Subst(false);
		}
		if (!gen.compose(Subst(p.first, p.second.term))) {
			return Subst(false);
		}
	}
	if (!intersects(com, gen)) {
		if (com.compose(gen)) {
			return com;
		} else {
			return Subst(false);
		}
	} else {
		MultyTree t1(com, gen);
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

	debug_unify_subs = (pr->ind == 1);

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
		/*if (pr->ind == 2 && ind.current_is({3, 0})) {
			cout << "AAA" << endl;
			debug_unify_subs_1 = pr->ind == 2 && ind.current_is({3, 0});
			debug_unify = pr->ind == 2 && ind.current_is({3, 0});
		}*/
		if (debug_unify_subs) {
			cout << "-------------" << endl;
		}
		MultyTree t(ch);
		Subst sub = unify_subs(t);
		if (sub.ok) {
			pr->proofs.emplace_back(new ProofProp(*pr, ch, sub));
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
			parent->proofs.push_back(make_unique<ProofExp>(*parent, p.get(), p->sub));
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


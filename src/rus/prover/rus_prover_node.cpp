#include "rus_prover_space.hpp"
#include "rus_prover_unify.hpp"
#include "rus_prover_down.hpp"

namespace mdl { namespace rus { namespace prover {

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
				for (auto& q : unify_down(parent, p.get())) {
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


#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

Node::~Node() {
	space->unregisterNode(this);
}

inline Symbol fresh_var(Symbol v, uint n) {
	return Symbol(
		Lex::toInt(Lex::toStr(v.lit) + "_" + to_string(n)),
		v.type()->id(),
		Symbol::VAR
	);
}

static void make_free_vars_fresh(const Assertion* a, Subst& s, map<uint, uint>& vars) {
	for (auto& v : a->vars.v) {
		if (!s.sub().count(v.lit)) {
			uint n = vars.count(v.lit) ? vars[v.lit] + 1 : 0;
			vars[v.lit] = n;
			s.join(v.lit, fresh_var(v, n));
		}
	}
}

Hyp::Hyp(const LightTree& e, Space* s) :
	Node(s), parent(nullptr), expr(e) {
	complete();
	space->registerNode(this);
}

Hyp::Hyp(const LightTree& e, Prop* p) :
	Node(p), parent(p), expr(p ? apply(p->sub, e) : e) {
	space->registerNode(this);
}

Prop::Prop(const PropRef& r, const Subst& s, Hyp* p) : Node(p), parent(p), prop(r), sub(s) {
	make_free_vars_fresh(r.ass, sub, space->vars);
	space->registerNode(this);
}

void Prop::buildUp() {
	for (auto& h : prop.ass->hyps) {
		//cout << "ASS HYP: " << rus::show(h->expr) << endl;
		//cout << "SUB: " << prover::show(sub) << endl;
		//cout << "NODE EXPR: " << prover::show(apply(sub, convert_tree(*h->expr.tree()))) << endl;

		Hyp* hyp = new Hyp(convert_tree(*h->expr.tree()), this);
		cout << "HYP EXPR: " << prover::show(hyp->expr) << endl;

		premises.emplace_back(hyp);
	}
	for (auto& p : premises) {
		p.get()->complete();
	}
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

	for (const auto& m : space->assertions.unify(expr)) {
		variants.emplace_back(new Prop(m.data, m.subs.first, this));
	}
}

void Hyp::complete() {
	for (const auto& m : space->hyps.match_back(expr)) {
		proofs.emplace_back(new ProofTop(*this, m.data, m.subs.second));
	}
	//cout << "COMPLETING: " << ind << endl;
	queue<Node*> downs;
	downs.push(this);
	while (!downs.empty()) {
		Node* n = downs.front();
		//cout << "DOWNING: " << n->ind << endl;
		downs.pop();
		for (auto x : n->buildDown()) {
			downs.push(x);
		}
	}
}

struct Ind {
	Ind() : size_(0), fixed_(-1), hasNext_(false), isEmpty_(false) { }

	void addDim(uint d) {
		++size_;
		if (d == 0) {
			isEmpty_ = true;
		}
		if (d > 1) {
			hasNext_ = true;
		}
		dims_.push_back(d);
		ind_.push_back(0);
	}
	void addFixed(uint i) {
		fixed_ = size_;
		++size_;
		dims_.push_back(-1);
		ind_.push_back(i);
	}
	void makeNext() {
		for (uint i = 0; i < size_; ++ i) {
			if (dims_[i] == -1) {
				continue;
			}
			if (ind_[i] + 1 < dims_[i]) {
				++ ind_[i];
				hasNext_ =
					(ind_[i] + 1 < dims_[i]) ||
					((i + 1 < size_) && (fixed_ + 1 != size_));
				return;
			} else {
				ind_[i] = 0;
			}
		}
		assert(false && "this execution point should be unreacheable");
	}
	bool hasNext() const {
		return size_ && hasNext_;
	}
	bool empty() const {
		return size_ && isEmpty_;
	}
	uint size() const {
		return size_;
	}
	uint operator[] (uint i) const {
		return ind_[i];
	}
	string show() const {
		if (empty()) return "empty";
		string ret;
		ret += "size: " + to_string(size_) + ", ";
		ret += "dims: [";
		for (auto d : dims_) {
			ret += (d == -1 ? string("N") : to_string(d)) + " ";
		}
		ret += "]";
		return ret;
	}
	string current() const {
		if (empty()) return "empty";
		string ret = "[";
		for (auto i : ind_) {
			ret += to_string(i) + " ";
		}
		ret += "]";
		return ret;
	}

private:
	uint         size_;
	uint         fixed_;
	vector<uint> dims_;
	vector<uint> ind_;
	bool         hasNext_;
	bool         isEmpty_;
};

struct Unified {
	Unified(bool ok = false) : sub(ok), term(nullptr) { }
	Subst      sub;
	LightTree* term;
};


bool check_unification(const Unified& unif, const vector<const LightTree*>& ex) {
	for (auto e : ex) {
		if (apply(unif.sub, *e) != *unif.term) {
			return false;
		}
	}
	return true;
}


Unified unify(const vector<const LightTree*>& ex) {
	const Rule* r = nullptr;
	vector<LightSymbol> vars;

	//cout << "exps.size() = " << ex.size() << endl;
	//cout << "Exps:" << endl;
	//for (const auto& t : ex) {
	//	cout << "\t" << show(*t) << endl;
	//}
	//cout << endl;

	vector<const LightTree::Children*> rules;

	enum class UnifyKind {UNDEF, VAR, CONST, RULE, DEFAULT = UNDEF};
	UnifyKind kind = UnifyKind::DEFAULT;

	for (const auto& t : ex) {
		switch (t->kind()) {
		case LightTree::VAR:
			if (t->var().rep) {
				if (kind == UnifyKind::UNDEF) {
					kind = UnifyKind::VAR;
				} else if (kind != UnifyKind::VAR) {
					return Unified();
				}
				vars.push_back(t->var());
			} else {
				if (kind == UnifyKind::UNDEF) {
					kind = UnifyKind::CONST;
				} else if (kind != UnifyKind::CONST) {
					return Unified();
				}
			}
			break;
		case LightTree::NODE:
			if (kind == UnifyKind::UNDEF) {
				kind = UnifyKind::RULE;
			} else if (kind != UnifyKind::RULE) {
				return Unified();
			}
			if (!r) {
				r = t->rule();
			} else if (r != t->rule()) {
				return Unified();
			}
			rules.push_back(&t->children());
			break;
		default: assert(false && "no term in unify_both");
		}
	}
	Unified ret(true);
	if (r) {
		LightTree::Children ch;
		for (uint i = 0; i < r->arity(); ++ i) {
			vector<const LightTree*> x;
			for (const auto t : rules) {
				x.push_back((*t)[i].get());
			}
			Unified s = unify(x);
			if (!ret.sub.join(s.sub)) {
				//cout << "A" << endl;
				return Unified();
			}
			ch.push_back(make_unique<LightTree>(*s.term));
		}
		ret.term = new LightTree(r, ch);
		for (auto s : vars) {
			if (r->type() == s.type) {
				ret.sub.join(Subst(s.lit, *ret.term));
			} else if (Rule* sup = find_super(r->type(), s.type)) {
				ret.sub.join(Subst(s.lit, LightTree(sup, new LightTree(*ret.term))));
			} else {
				//cout << "B" << endl;
				return Unified();
			}
		}
	} else {
		std::sort(
			vars.begin(),
			vars.end(),
			[](const LightSymbol& v1, const LightSymbol& v2) {
				return *v1.type < *v2.type;
			}
		);
		LightSymbol lv;
		if (!vars.size()) {
			//cout << "C: " << show(lv) << " == ";
			for (const auto& t : ex) {
				if (t->kind() == LightTree::VAR) {
					if (lv.lit == -1) {
						lv = t->var();
					} else if (t->var() != lv) {
						return Unified();
					}
				} else {
					return Unified();
				}
				//cout << show(t->var()) << " ";
			}
			//cout << "\nC!" << endl;
		} else {
			for (auto s : vars) {
				if (lv.lit == -1) {
					lv = s;
				}
				if (lv.type == s.type) {
					ret.sub.join(Subst(s.lit, lv));
				} else if (Rule* sup = find_super(lv.type, s.type)) {
					ret.sub.join(Subst(s.lit, LightTree(sup, new LightTree(lv))));
				} else {
					//cout << "D" << endl;
					return Unified();
				}
			}
		}
		ret.term = new LightTree(lv);
	}
	//cout << "E" << endl;
	//exit(0);
	/*if (!check_unification(ret, ex)) {
		cout << "AAAAA" << endl;
	} else {
		cout << "OK" << endl;
	}*/
	return ret;
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
			if (s.sub.ok()) {
				ret.msub_[p.first] = s;
			} else {
				ret.ok = false;
				break;
			}
		}
		return ret;
	}

private:
	void add(const Subst& s) {
		for (const auto& p : s.sub())
			msub_[p.first].push_back(&p.second);
	}
	map<uint, vector<const LightTree*>> msub_;
};

inline bool intersects(const Subst& s1, const Subst& s2) {
	for (const auto& p : s1.sub()) {
		if (s2.sub().count(p.first)) return true;
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
		if (!com.join(p.second.sub)) return Subst(false);
		if (!gen.join(p.first, *p.second.term)) Subst(false);
	}
	if (!intersects(com, gen)) {
		com.join(gen);
		return com;
	} else {
		MultyTree t1(com, gen);
		return unify_subs(t1);
	}
}

vector<Node*> unify_subs(Prop* pr, ProofHyp* h) {
	vector<ProofHyp*> proofs;
	Ind ind;
	for (auto& x : pr->premises) {
		if (x.get() != &h->node) {
			ind.addDim(x.get()->proofs.size());
		} else {
			ind.addFixed(find_in_vector(x.get()->proofs, h));
		}
	}
	if (ind.empty()) {
		return vector<Node*>();
	}
	//cout << endl << "IND: " << ind.show() << endl << endl;
	bool new_proofs = false;
	while (true) {
		vector<ProofHyp*> ch;
		//cout << "CURRENT: " << ind.current() << endl;
		//cout << "UNIFYING: \n--------------" << endl;
		//cout << "PROP: " << pr->ind << endl;
		for (uint i = 0; i < ind.size(); ++ i) {
			ProofHyp* ph = pr->premises[i].get()->proofs[ind[i]].get();
			//cout << i << ": " << show(ph->expr) << "\nsub: \n" << show(ph->sub) << endl;
			ch.push_back(ph);
		}
		//cout << "-------------" << endl;
		MultyTree t(ch);
		Subst sub = unify_subs(t);
		if (sub.ok()) {
			pr->proofs.emplace_back(new ProofProp(*pr, ch, sub));
			//cout << "OK:\n" << show(sub) << endl;
			new_proofs = true;
		} else {
			//cout << "FAIL" << endl;
		}
		//cout << endl << endl << endl;
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
			parent->proofs.push_back(make_unique<ProofExp>(*parent, p.get()));
			new_proofs = true;
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
				for (auto& q : unify_subs(parent, p.get())) {
					ret.push_back(q);
				}
			}
		}
	}
	return ret;
}

}}}


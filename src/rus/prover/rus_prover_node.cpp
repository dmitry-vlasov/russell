#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

Node::Node(Space* s) : space(s), ind(-1) {
	space->registerNode(this);
}

Node::Node(Node* n) : space(n->space), ind(-1) {
	space->registerNode(this);
}

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

Prop::Prop(const PropRef& r, const Subst& s, Hyp* p) : Node(p), parent(p), prop(r), sub(s) {
	make_free_vars_fresh(r.ass, sub, space->vars);
}

void Prop::buildUp() {
	for (auto& h : prop.ass->hyps) {
		premises.emplace_back(new Hyp(apply(sub, convert_tree(*h.get()->expr.tree())), this));
	}
	for (auto& p : premises) {
		p.get()->complete();
	}
}

void Hyp::complete() {
	for (const auto& p : space->hyps.match_back(expr)) {
		proofs.emplace_back(new ProofTop(*this, p.first, p.second));
	}
	queue<Node*> downs;
	downs.push(this);
	while (!downs.empty()) {
		Node* n = downs.front(); downs.pop();
		for (auto x : n->buildDown()) {
			downs.push(x);
		}
	}
}

void Hyp::buildUp() {
	for (const auto& p : space->assertions.match_forth(expr)) {
		if (p.first.ass->token.preceeds(space->prop.ass->token)) {
			variants.emplace_back(new Prop(p.first, p.second, this));
		}
	}
}

struct Ind {
	Ind() : size_(0), hasNext_(true), isEmpty_(false) { }

	void addDim(uint d) {
		++size_;
		if (d == 0) {
			isEmpty_ = true;
		}
		dims_.push_back(d);
		ind_.push_back(0);
	}
	void addFixed(uint i) {
		++size_;
		dims_.push_back(-1);
		ind_.push_back(i);
	}
	void makeNext() {
		for (uint i = 0; i < size_; ++ i) {
			if (dims_[i] == -1) continue;
			if (ind_[i] + 1 < dims_[i]) {
				++ ind_[i];
				break;
			} else {
				ind_[i] = 0;
			}
		}
		hasNext_ = false;
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

private:
	uint         size_;
	vector<uint> dims_;
	vector<uint> ind_;
	bool         hasNext_;
	bool         isEmpty_;
};

struct Unified {
	Unified() : sub(false), term(nullptr) { }
	operator bool() const{
		return sub;
	}
	Subst      sub;
	LightTree* term;
};

Unified unify(const vector<const LightTree*>& ex) {
	const Rule* r = nullptr;
	vector<LightSymbol> vars;
	vector<const LightTree::Children*> rules;
	for (const auto& t : ex) {
		switch (t->kind()) {
		case LightTree::VAR: vars.push_back(t->var()); break;
		case LightTree::NODE:
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
	Unified ret;
	if (r) {
		LightTree::Children ch;
		for (uint i = 0; i < r->arity(); ++ i) {
			vector<const LightTree*> x;
			for (const auto t : rules) {
				x.push_back((*t)[i].get());
			}
			Unified s = unify(x);
			if (!ret.sub.join(s.sub)) {
				return Unified();
			}
			ch.push_back(make_unique<LightTree>(*ret.term));
		}
		ret.term = new LightTree(r, ch);
		for (auto s : vars) {
			if (r->type() == s.type) {
				ret.sub.join(Subst(s.lit, *ret.term));
			} else if (Rule* sup = find_super(r->type(), s.type)) {
				ret.sub.join(Subst(s.lit, LightTree(sup, new LightTree(*ret.term))));
			} else return Unified();
		}
	} else {
		std::sort(
			vars.begin(),
			vars.end(),
			[](const LightSymbol& v1, const LightSymbol& v2) {
				return *v1.type < *v2.type;
			}
		);
		LightSymbol lv = *vars.begin();
		for (auto s : vars) {
			if (lv.type == s.type) {
				ret.sub.join(Subst(s.lit, lv));
			} else if (Rule* sup = find_super(lv.type, s.type)) {
				ret.sub.join(Subst(s.lit, LightTree(sup, new LightTree(lv))));
			} else return Unified();
		}
	}
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
			if (Unified s = unify(p.second)) {
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
	while (true) {
		vector<ProofHyp*> ch;
		cout << "UNIFYING: \n--------------" << endl;
		for (uint i = 0; i < ind.size(); ++ i) {
			ProofHyp* ph = pr->premises[i].get()->proofs[ind[i]].get();
			cout << i << ": " << show(ph->expr) << "\nsub: \n" << show(ph->sub) << endl;
			ch.push_back(ph);
		}
		cout << "-------------" << endl;
		MultyTree t(ch);
		Subst sub = unify_subs(t);
		if (sub) {
			pr->proofs.emplace_back(new ProofProp(*pr, ch, sub));
			cout << "OK:\n" << show(sub) << endl;
		} else {
			cout << "FAIL" << endl;
		}
		cout << endl << endl << endl;
		if (!ind.hasNext()) {
			break;
		}
		ind.makeNext();
	}
	return {pr};
}

vector<Node*> Prop::buildDown() {
	for (auto& p : proofs) {
		if (p->new_) {
			parent->proofs.push_back(make_unique<ProofExp>(*parent, p.get()));
		}
	}
	return {parent};
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


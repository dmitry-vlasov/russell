#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

Node::~Node() {
	for (auto n : child) delete n;
	for (auto p : proof) delete p;
}

Prop::Prop(const PropRef& r, const Substitution& s, Node* p) :
	Node(p), prop_(r), sub_(s) {
	space->leaf_props.insert(this);
	if (parent && parent->parent) {
		space->leaf_props.erase(dynamic_cast<Prop*>(parent->parent));
	}
}

void Hyp::complete() {
	space->leaf_hyps.insert(this);
	if (parent && parent->parent) {
		space->leaf_hyps.erase(dynamic_cast<Hyp*>(parent->parent));
	}
	for (const auto& p : space->hyps.unify_back(expr_.tree))
		proof.push_back(new ProofHyp(p.first, p.second));
	queue<Node*> downs;
	downs.push(this);
	while (true) {
		Node* n = downs.front(); downs.pop();
		for (auto x: n->buildDown()) downs.push(x);
		if (downs.empty()) break;
	}
}

vector<Node*> Hyp::buildUp() {
	vector<Node*> ret;
	for (const auto& p : assertion_index().unify_forth(expr_.tree))
		ret.push_back(new Prop(p.first, p.second, this));
	return ret;
}

vector<Node*> Prop::buildUp() {
	vector<Node*> ret;
	for (rus::Hyp* h : prop_.assertion()->hyps)
		ret.push_back(new Hyp(h->expr, this));
	return ret;
}

vector<Node*> Ref::buildUp() {
	vector<Node*> ret;
	return ret;
}

struct Ind {
	Ind() : size_(0), hasNext_(true) { }

	void addDim(uint d) {
		++size_;
		if (d == 0) hasNext_ = false;
		else {
			dims_.push_back(d);
			ind_.push_back(0);
		}
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
			} else ind_[i] = 0;
		}
		hasNext_ = false;
	}
	bool hasNext() const {
		return size_ && hasNext_;
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
};

struct UnifSym {
	UnifSym() : sub(false) { }
	operator bool() const{
		return sub;
	}
	Substitution sub;
	Tree term;
};

UnifSym unify_both(const vector<const Tree*>& ex) {
	const Rule* r = nullptr;
	vector<const Symbol*> vars;
	vector<const Tree::Children*> rules;
	for (const auto& t : ex) {
		switch (t->kind) {
		case Tree::VAR: vars.push_back(t->var()); break;
		case Tree::NODE:
			if (!r) r = t->rule();
			else if (r != t->rule()) return UnifSym();
			rules.push_back(&t->children());
			break;
		default: assert(false && "no term in unify_both");
		}
	}
	UnifSym ret;
	if (r) {
		Tree::Children ch;
		for (uint i = 0; i < r->arity(); ++ i) {
			vector<const Tree*> x;
			for (const auto t : rules) {
				x.push_back((*t)[i].get());
			}
			UnifSym s = unify_both(x);
			if (!ret.sub.join(s.sub)) return UnifSym();
			ch.emplace_back(new Tree(ret.term));
		}
		ret.term = Tree(r->id(), ch);
		for (auto s : vars) {
			if (r->type() == s->type()) {
				ret.sub.join(Substitution(*s, ret.term));
			} else if (Rule* sup = find_super(r->type(), s->type())) {
				ret.sub.join(Substitution(*s, Tree(sup->id(), {new Tree(ret.term)})));
			} else return UnifSym();
		}
	} else {
		std::sort(
			vars.begin(),
			vars.end(),
			[](const Symbol* v1, const Symbol* v2) {
				return *v1->type() < *v2->type();
			}
		);
		const Symbol* lv = *vars.begin();
		for (auto s : vars) {
			if (lv->type() == s->type()) {
				ret.sub.join(Substitution(*s, *lv));
			} else if (Rule* sup = find_super(lv->type(), s->type())) {
				ret.sub.join(Substitution(*s, Tree(sup->id(), {new Tree(*lv)})));
			} else return UnifSym();
		}
	}
	return ret;
}

struct MultySub {
	MultySub() : ok(true) { }
	map<Symbol, UnifSym> msub_;
	bool ok;
};

struct MultyTree {
	MultyTree(const Substitution& s1, const Substitution& s2) {
		add(s1);
		add(s2);
	}
	MultyTree(const vector<Proof*>& ch) {
		for (auto p : ch) add(p->sub());
	}
	MultySub makeSubs() const {
		MultySub ret;
		for (const auto& p : msub_) {
			if (UnifSym s = unify_both(p.second)) {
				ret.msub_[p.first] = s;
			} else {
				ret.ok = false;
				break;
			}
		}
		return ret;
	}

private:
	void add(const Substitution& s) {
		for (const auto& p : s.sub())
			msub_[p.first].push_back(&p.second);
	}
	map<Symbol, vector<const Tree*>> msub_;
};

bool intersects(const Substitution& s1, const Substitution& s2) {
	for (const auto& p : s1.sub())
		if (s2.sub().count(p.first)) return true;
	return false;
}

Substitution unify_subs(const MultyTree& t) {
	MultySub m = t.makeSubs();
	Substitution com;
	Substitution gen;
	for (auto& p : m.msub_) {
		if (!com.join(p.second.sub)) return Substitution(false);
		if (!gen.join(p.first, p.second.term)) Substitution(false);
	}
	if (!intersects(com, gen)) {
		com.join(gen);
		return com;
	} else {
		MultyTree t1(com, gen);
		return unify_subs(t1);
	}
}

Proof* unify_subs(Node* pr, Proof* p, vector<Proof*> ch) {
	MultyTree t(ch);
	Substitution sub = unify_subs(t);
	Proof* ret = new ProofStep(pr, std::move(ch), sub);
	p->setParent(ret);
	return ret;
}

inline uint find_index(const vector<Proof*> pv, const Proof* p) {
	return std::find(pv.begin(), pv.end(), p) - pv.begin();
}

vector<Node*> unify_subs(Node* n, Proof* p) {
	vector<Proof*> proofs;
	assert(n->kind() == Node::HYP);
	Prop* pr = prop(n->parent);
	Ind ind;
	for (auto x : pr->child) {
		if (x != n) ind.addDim(x->proof.size());
		else ind.addFixed(find_index(x->proof, p));
	}
	while (true) {
		vector<Proof*> ch;
		for (uint i = 0; i < ind.size(); ++ i)
			ch.push_back(pr->child[i]->proof[ind[i]]);
		pr->proof.push_back(unify_subs(pr, p, ch));
		if (!ind.hasNext()) break;
		ind.makeNext();
	}
	return {pr};
}

vector<Node*> Prop::buildDown() {
	vector<Node*> ret;
	for (auto p : proof)
		if (p->isNew()) {
			p->setParent(new ProofStep(this, {p}));
			parent->proof.push_back(p->parent());
			ret.push_back(parent);
		}
	return ret;
}

vector<Node*> Hyp::buildDown() {
	vector<Node*> ret;
	for (auto p : proof)
		if (p->isNew()) {
			for (auto q : unify_subs(this, p))
				ret.push_back(q);
		}
	return ret;
}

vector<Node*> Ref::buildDown() {
	vector<Node*> ret;
	return ret;
}

}}}


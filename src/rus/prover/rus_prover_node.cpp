#include "rus_prover_space.hpp"

namespace mdl { namespace rus { namespace prover {

Node::Node(Space* s) :
	parent(nullptr), space(s), ind(-1) {
}
Node::Node(Node* p) :
	parent(p), space(p->space), ind(-1) {
	if (p) p->child.push_back(this);
}

Node::~Node() {
	for (auto n : child) delete n;
	for (auto p : proof) delete p;
}

inline Symbol fresh_var(Symbol v, uint n) {
	return Symbol(
		Lex::toInt(Lex::toStr(v.lit) + "_" + to_string(n)),
		v.type()->id(),
		Symbol::VAR
	);
}

static void make_free_vars_fresh(const Assertion* a, Substitution& s, map<uint, uint>& vars) {
	for (auto& v : a->vars.v) {
		if (!s.sub().count(v)) {
			uint n = vars.count(v.lit) ? vars[v.lit] + 1 : 0;
			vars[v.lit] = n;
			s.join(v, fresh_var(v, n));
		}
	}
}

Prop::Prop(const PropRef& r, const Substitution& s, Node* p) :
	Node(p), prop_(r), sub_(s) {
	make_free_vars_fresh(r.assertion(), sub_, space->vars);
	space->registerNode(this);
}

void Hyp::complete() {
	for (const auto& p : space->hyps.unify_back(expr_.tree)) {
		proof.push_back(new ProofHyp(p.first, p.second));
	}
	queue<Node*> downs;
	downs.push(this);
	while (true) {
		Node* n = downs.front(); downs.pop();
		for (auto x: n->buildDown()) downs.push(x);
		if (downs.empty()) break;
	}
	space->registerNode(this);
}

vector<Node*> Hyp::buildUp() {
	vector<Node*> ret;
	for (const auto& p : assertion_index().unify_forth(expr_.tree)) {
		cout << "unified assertion " << show_id(p.first.assertion()->id()) << endl;
		ret.push_back(new Prop(p.first, p.second, this));
	}
	return ret;
}

vector<Node*> Prop::buildUp() {
	vector<Node*> ret;
	for (rus::Hyp* h : prop_.assertion()->hyps)
		ret.push_back(new Hyp(apply(sub_, h->expr), this));
	return ret;
}

vector<Node*> Ref::buildUp() {
	vector<Node*> ret;
	return ret;
}

struct Ind {
	Ind() : size_(0), hasNext_(true), isEmpty_(false) { }

	void addDim(uint d) {
		++size_;
		if (d == 0) isEmpty_ = true;
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
			} else ind_[i] = 0;
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
	MultyTree(const vector<ProofElem*>& ch) {
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

inline bool intersects(const Substitution& s1, const Substitution& s2) {
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

ProofElem* unify_subs(Node* pr, ProofElem* p, vector<ProofElem*> ch) {
	MultyTree t(ch);
	Substitution sub = unify_subs(t);
	return new ProofStep(pr, std::move(ch), sub);
}

inline uint find_index(const vector<ProofElem*> pv, const ProofElem* p) {
	return std::find(pv.begin(), pv.end(), p) - pv.begin();
}

vector<Node*> unify_subs(Node* n, ProofElem* p) {
	if (!n->parent) return vector<Node*>();
	vector<ProofElem*> proofs;
	assert(n->kind() == Node::HYP);
	Prop* pr = prop(n->parent);
	Ind ind;
	for (auto x : pr->child) {
		if (x != n) ind.addDim(x->proof.size());
		else ind.addFixed(find_index(x->proof, p));
	}
	if (ind.empty()) return vector<Node*>();
	while (true) {
		vector<ProofElem*> ch;
		for (uint i = 0; i < ind.size(); ++ i)
			ch.push_back(pr->child[i]->proof[ind[i]]);
		pr->proof.push_back(unify_subs(pr, p, ch));
		if (!ind.hasNext()) break;
		ind.makeNext();
	}
	return {pr};
}

vector<Node*> Prop::buildDown() {
	for (auto p : proof)
		if (p->isNew()) {
			parent->proof.push_back(new ProofStep(this, {p}));
		}
	return {parent};
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


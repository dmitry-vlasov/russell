#include "rus_prover_space.hpp"
#include "rus_prover_unify.hpp"

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
		if (!s.sub.count(v.lit)) {
			uint n = vars.count(v.lit) ? vars[v.lit] + 1 : 0;
			vars[v.lit] = n;
			s.sub[v.lit] = LightTree(fresh_var(v, n));
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
		//cout << "HYP THIS: " << prover::show(expr) << endl;
		//cout << "PROP UP: " << Lex::toStr(m.data.id()) << endl;
		//cout << "SUB:" << endl << prover::show(m.sub) << endl;
		variants.emplace_back(new Prop(m.data, m.sub, this));
	}
}

void Hyp::complete() {
	for (const auto& m : space->hyps.unify(expr)) {
		proofs.emplace_back(new ProofTop(*this, m.data, m.sub));
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
		if (!com.join(p.second.sub)) {
			return Subst(false);
		}
		if (!gen.join(p.first, p.second.term)) {
			return Subst(false);
		}
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
		if (sub.ok) {
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


#include "rus_prover_index.hpp"

namespace mdl { namespace rus { namespace prover {

vector<Node*> build_up(Node* n) {
	vector<Node*> ret;
	switch (n->kind()) {
	case Node::REF: break;
	case Node::HYP: {
		for (const auto& p : assertion_index().unify_forth(hyp(n)->expr.tree))
			ret.push_back(new Prop(p.first, p.second, n));
		break;
	}
	case Node::PROP:
		for (rus::Hyp* h : prop(n)->prop.ass.get()->hyps)
			ret.push_back(new Hyp(h->expr, n));
		break;
	}
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
		ret.term = Tree(const_cast<Rule*>(r), ch);
		for (auto s : vars) {
			if (r->type() == s->type()) {
				ret.sub.join(Substitution(*s, ret.term));
			} else if (Rule* sup = find_super(r->type(), s->type())) {
				ret.sub.join(Substitution(*s, Tree(sup, {new Tree(ret.term)})));
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
				ret.sub.join(Substitution(*s, Tree(sup, {new Tree(*lv)})));
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
	void add(const Substitution& s) {
		for (const auto& p : s.sub())
			msub_[p.first].push_back(&p.second);
	}
	MultySub makeSubs() {
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
	map<Symbol, vector<const Tree*>> msub_;
};

Node* unify_subs(vector<Proof*> ch) {
	MultyTree t;
	for (auto p : ch) t.add(p->sub);
	MultySub m = t.makeSubs();
	return nullptr;
}

inline uint find_index(const vector<Proof*> pv, const Proof* p) {
	return std::find(pv.begin(), pv.end(), p) - pv.begin();
}

vector<Node*> unify_subs(Node* n, Proof* p) {
	vector<Node*> ret;
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
		ret.push_back(unify_subs(ch));
		if (!ind.hasNext()) break;
		ind.makeNext();
	}
	return ret;
}

vector<Node*> build_down(Node* n) {
	vector<Node*> ret;
	switch (n->kind()) {
	case Node::REF: break;
	case Node::HYP:
		for (auto p : n->proof)
			if (p->new_) {
				p->new_ = false;
				for (auto q : unify_subs(n, p))
					ret.push_back(q);
			}
		break;
	case Node::PROP:
		for (auto p : n->proof)
			if (p->new_) {
				p->new_ = false;
				p->parent = new Proof{n, nullptr, {p}, true};
				n->parent->proof.push_back(p->parent);
				ret.push_back(n->parent);
			}
		break;
	}
	return ret;
}

}}}


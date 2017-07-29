#pragma once

#include "rus_ast.hpp"

namespace mdl { namespace rus {

Rule* find_super(const Type* type, const Type* super);

namespace prover {

class Proof;
class Prop;
class Hyp;
class Ref;

struct Node {
	enum Kind { PROP, HYP, REF };
	Node*          parent;
	vector<Node*>  child;
	vector<Proof*> proof;
	Node(Node* p) : parent(p) { if (p) p->child.push_back(this); }
	virtual Kind kind() const = 0;
	virtual ~Node();
};

Prop* prop(Node* n);
Hyp*  hyp (Node* n);
Ref*  ref (Node* n);

struct PropRef {
	User<Assertion> ass;
	uint prop;
};

inline bool operator < (const PropRef& a1, const PropRef& a2) {
	return a1.ass == a2.ass ? a1.prop  < a2.prop : a1.ass < a2.ass;
}

struct Prop : public Node {
	PropRef      prop;
	Substitution sub;
	Prop(PropRef r, const Substitution& s, Node* p) :
		Node(p), prop(r), sub(s) { }
	Kind kind() const { return PROP; }
};

struct Hyp : public Node {
	Expr expr;
	Hyp(const Expr& e, Node* p = nullptr) :
		Node(p), expr(p ? apply(prop(p)->sub, e) : e) { }
	Kind kind() const { return HYP; }
};

struct Ref : public Node {
	Node* node;
	Substitution sub;
	Ref(Node* n, const Substitution& s, Node* p) :
		Node(p), node(n), sub(s) { }
	Kind kind() const { return REF; }
};

struct Proof {
	Node*          node;
	Proof*         parent;
	vector<Proof*> child;
	Substitution*  sub;
	bool           new_;
	~Proof() {
		delete sub;
		for (auto n : child) delete n;
	}
};

inline Node::~Node()  {
	for (auto n : child) delete n;
	for (auto p : proof) delete p;
}

inline Prop* prop(Node* n) { return dynamic_cast<Prop*>(n); }
inline Hyp*  hyp (Node* n) { return dynamic_cast<Hyp*>(n); }
inline Ref*  ref (Node* n) { return dynamic_cast<Ref*>(n); }

template<class D>
using Unified = map<D, Substitution>;

template<class D>
struct Index {
	typedef D Data;
	struct Node {
		vector<Data>   data;
		vector<Index*> child;
	};
	map<User<Rule>, Node>     rules;
	map<Symbol, vector<Data>> vars;

	void add(const Tree*, const Data&);
	Unified<Data> unify(const Tree*) const;
	~Index();
};

template<class D>
void Index<D>::add(const Tree* t, const D& d) {
	if (t->kind == Tree::VAR) {
		vars[*t->var()].push_back(d);
	} else {
		if (!t->children().size())
			rules[t->rule()].data.push_back(d);
		else {
			bool is_new = !rules.count(t->rule());
			vector<Index<D>*>& ch = rules[t->rule()].child;
			if (is_new)
				for (const auto& c : t->children())
					ch.push_back(new Index<D>);
			auto i = ch.begin();
			for (const auto& c : t->children()) {
				(*(i++))->add(c.get(), d);
			}
		}
	}
}

template<class D>
void intersect(Unified<D>& u, Unified<D> w[], uint sz) {
	for (auto p : w[0]) {
		D d = p.first;
		Substitution s = p.second;
		int i = 1;
		for (; i < sz; ++ i)
			if (!w[i].count(d) || !s.join(w[i][d]))
				break;
		if (i == sz) u[d] = s;
	}
}

template<class D>
Unified<D> Index<D>::unify(const Tree* t) const {
	Unified<Data> unif;
	for (const auto& p : vars) {
		Symbol v = p.first;
		if (v.type() == t->type()) {
			for (const Data& d : p.second)
				unif[d].join(v, t);
		} else if (Rule* super = find_super(t->type(), v.type())) {
			for (const Data& d : p.second) {
				Tree tr(super, {new Tree(*t)});
				unif[d].join(v, &tr);
			}
		}
	}
	if (rules.count(t->rule())) {
		const Node& n = rules.at(t->rule());
		for (const Data& d : n.data) unif[d];
		auto ch = t->children().begin();
		Unified<Data> un[n.child.size()];
		int c = 0;
		for (const Index* i : n.child) {
			un[c++] = i->unify((ch++)->get());
		}
		if (c > 0) intersect(unif, un, c);
	}
	return unif;
}

template<class D>
Index<D>::~Index() {
	for (auto& p : rules)
		for (auto& i : p.second.child)
			delete i;
}


Index<PropRef>& assertion_index();

vector<Node*> build_up(Node*);
void build_down(vector<Node*>);

}}}


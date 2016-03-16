#pragma once

#include "common.hpp"
#include "rus/expr.hpp"

namespace mdl { namespace rus {

struct Consts {
	vector<Symbol> symbols;
};

struct Vars {
	vector<Symbol> symbols;
};

struct Rule;

struct Type {
	uint name;
	vector<Type*> super;
	vector<Type*> infer;
	Tree<Rule*>   rules;
};

struct Rule {
	Type* type;
	Vars  vars;
	Expr  term;
};

struct Disj {
	vector<Symbol> vars;
};

struct Hyp {
	uint index;
	Expr expr;
};

struct Prop {
	uint index;
	Expr expr;
};

struct Proof;

struct Assertion {
	Vars          vars;
	vector<Disj*> disjs;
	vector<Hyp*>  hyps;
	vector<Prop*> props;
	Location      loc;
};

struct Axiom {
	Assertion ass;
};

struct Def {
	Assertion def;
	Assertion ass;
};

struct Proof;

struct Theorem {
	Assertion      ass;
	vector<Proof*> proofs;
};

struct Step;
struct Claim;
struct Qed;

struct Ref {
	enum Kind {
		NONE,
		HYP,
		PROP,
		STEP,
		CLAIM,
		QED
	};
	union Value {
		void*  non;
		Hyp*   hyp;
		Prop*  prop;
		Step*  step;
		Claim* claim;
		Qed*   qed;
	};
	Ref() : kind(NONE), val() { val.non = nullptr; }
	Ref(Hyp* h)   : kind(HYP),  val()  { val.hyp = h; }
	Ref(Prop* p)  : kind(PROP), val()  { val.prop = p; }
	Ref(Step* s)  : kind(STEP), val()  { val.step = s; }
	Ref(Claim* c) : kind(CLAIM), val() { val.claim = c; }
	Ref(Qed* q)   : kind(QED), val()   { val.qed = q; }
	void destroy();

	Kind kind;
	Value val;
};


struct Step {
	uint        index;
	Expr        expr;
	vector<Ref> refs;
	Assertion*  ass;
	Sub<>       sub;
};

struct Qed {
	uint  index;
	Prop* prop;
	Step* step;
};

struct Claim {
	uint        index;
	Expr        expr;
	vector<Ref> refs;
	Proof*      proof;
};

struct Proof {
	Proof() : steps(), theorem(nullptr) { }
	~ Proof();
	vector<Ref> steps;
	vector<Ref> roots;
	Assertion*  theorem;
};

class Theory;
class Import;

struct Node {
	enum Kind {
		NONE,
		CONST,
		TYPE,
		RULE,
		AXIOM,
		DEF,
		THEOREM,
		PROOF,
		THEORY,
		IMPORT
	};
	union Value {
		void*      non;
		Consts*    cst;
		Type*      tp;
		Rule*      rul;
		Axiom*     ax;
		Def*       def;
		Theorem*   thm;
		Proof*     prf;
		Theory*    thy;
		Import*    imp;
	};

	Node() : kind(NONE), val() { val.non = nullptr; }
	Node(Consts* c)  : kind(CONST),   val() { val.cst = c; }
	Node(Type* t)    : kind(TYPE),    val() { val.tp  = t; }
	Node(Rule* r)    : kind(RULE),    val() { val.rul = r; }
	Node(Axiom* a)   : kind(AXIOM),   val() { val.ax  = a; }
	Node(Def* d)     : kind(DEF),     val() { val.def = d; }
	Node(Theorem* t) : kind(THEOREM), val() { val.thm = t; }
	Node(Proof* p)   : kind(PROOF),   val() { val.prf = p; }
	Node(Theory* t)  : kind(THEORY),  val() { val.thy = t; }
	Node(Import* i)  : kind(IMPORT),  val() { val.imp = i; }
	void destroy();

	Kind kind;
	Value val;
};

struct Source;

struct Import {
	string  path;
	Source* source;
};

struct Theory {
	~ Theory() {
		for (auto& n : nodes)
			n.destroy();
	}
	uint         name;
	vector<Node> nodes;
};

struct Source {
	Source(const string& n) :
	top(false), name(n), contents() {
		static bool t = true; top = t; t = false;
	}
	bool   top;
	string name;
	Theory theory;
};

/*
inline void Node::destroy() {
	switch(type) {
	case NONE: break;
	case ASSERTION: delete val.ass; break;
	case CONSTANTS: delete val.cst; break;
	case SOURCE:    delete val.src; break;
	default : assert(false && "impossible");  break;
	}
	type = NONE;
}

inline void Ref::destroy() {
	if (type == PROOF)
		delete val.prf;
}

inline Proof::~ Proof() {
	for (auto& r : refs)
		r.destroy();
}
*/

ostream& operator << (ostream& os, const Consts&);
ostream& operator << (ostream& os, const Vars&);
ostream& operator << (ostream& os, const Type&);
ostream& operator << (ostream& os, const Rule&);
ostream& operator << (ostream& os, const Axiom&);
ostream& operator << (ostream& os, const Def&);
ostream& operator << (ostream& os, const Theorem&);
ostream& operator << (ostream& os, const Proof&);
ostream& operator << (ostream& os, const Step&);
ostream& operator << (ostream& os, const Ref&);
ostream& operator << (ostream& os, const Qed&);
ostream& operator << (ostream& os, const Claim&);
ostream& operator << (ostream& os, const Hyp&);
ostream& operator << (ostream& os, const Prop&);
ostream& operator << (ostream& os, const Node&);
ostream& operator << (ostream& os, const Import&);
ostream& operator << (ostream& os, const Theory&);
ostream& operator << (ostream& os, const Source&);

}} // mdl::rus

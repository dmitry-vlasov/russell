#pragma once

#include "common.hpp"
#include "rus/expr.hpp"

namespace mdl { namespace rus {

struct Const {
	Symbol symb;
	Symbol ascii;
	Symbol latex;
};

struct Vars {
	vector<Symbol> v;
};

struct Disj {
	vector<vector<Symbol>> d;
};

struct Rule;

struct Type {
	uint id;
	vector<Type*> sup;
	vector<Type*> inf;
	//Tree<Rule*>   rules;
};

struct Rule {
	uint  id;
	Type* type;
	Vars  vars;
	Expr  term;
};

inline Type* Expr::type() { return term.rule->type; }

struct Hyp {
	uint ind;
	Expr expr;
};

struct Prop {
	uint ind;
	Expr expr;
};

struct Proof;

struct Assertion {
	uint id;
	Vars vars;
	Disj disj;
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
	uint        ind;
	Expr        expr;
	vector<Ref> refs;
	Assertion*  ass;
	Sub<>       sub;
};

struct Qed {
	Prop* prop;
	Step* step;
};

struct Proof {
	Proof() :
	id(-1), vars(), steps(),
	roots(), theorem(nullptr) { }
	~ Proof();
	uint        id;
	Vars        vars;
	vector<Ref> steps;
	vector<Ref> roots;
	Assertion*  theorem;
};

struct Claim {
	uint        ind;
	Expr        expr;
	vector<Ref> refs;
	Proof       proof;
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
		void*    non;
		Const*   cst;
		Type*    tp;
		Rule*    rul;
		Axiom*   ax;
		Def*     def;
		Theorem* thm;
		Proof*   prf;
		Theory*  thy;
		Import*  imp;
	};

	Node() : kind(NONE), val() { val.non = nullptr; }
	Node(Const* c)   : kind(CONST),   val() { val.cst = c; }
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
	Theory() : id(-1), nodes(), parent(nullptr) { }
	Theory(uint n, Theory* p) : id(n), nodes(), parent(p) { }
	~ Theory() {
		for (auto& n : nodes)
			n.destroy();
	}
	uint         id;
	vector<Node> nodes;
	Theory*      parent;
};

struct Source {
	Source(const string& n) :
	top(false), name(n), theory() {
		static bool t = true; top = t; t = false;
	}
	bool   top;
	string name;
	Theory theory;
};

inline void Node::destroy() {
	switch(kind) {
	case CONST:   delete val.cst; break;
	case TYPE:    delete val.tp;  break;
	case RULE:    delete val.rul; break;
	case AXIOM:   delete val.ax;  break;
	case DEF:     delete val.def; break;
	case THEOREM: delete val.thm; break;
	case PROOF:   delete val.prf; break;
	case THEORY:  delete val.thy; break;
	case IMPORT:  delete val.imp; break;
	default : assert(false && "impossible"); break;
	}
	kind = NONE;
}


inline void Ref::destroy() {
	switch (kind) {
	case STEP : delete val.step; break;
	case CLAIM: delete val.claim; break;
	case QED:   delete val.qed; break;
	default : assert(false && "impossible"); break;
	}
	kind = NONE;
}

inline Proof::~ Proof() {
	for (auto& s : steps)
		s.destroy();
}

string show(const Const&);
string show(const Vars&);
string show(const Disj&);
string show(const Type&);
string show(const Rule&);
string show(const Axiom&);
string show(const Def&);
string show(const Theorem&);
string show(const Proof&);
string show(const Step&);
string show(const Ref&);
string show(const Qed&);
string show(const Claim&);
string show(const Hyp&);
string show(const Prop&);
string show(const Node&);
string show(const Import&);
string show(const Theory&);
string show(const Source&);

inline ostream& operator << (ostream& os, const Const& c) { os << show(c); return os; }
inline ostream& operator << (ostream& os, const Vars& v)  { os << show(v); return os; }
inline ostream& operator << (ostream& os, const Disj& d)  { os << show(d); return os; }
inline ostream& operator << (ostream& os, const Type& t)  { os << show(t); return os; }
inline ostream& operator << (ostream& os, const Rule& r)  { os << show(r); return os; }
inline ostream& operator << (ostream& os, const Axiom& a) { os << show(a); return os; }
inline ostream& operator << (ostream& os, const Def& d)   { os << show(d); return os; }
inline ostream& operator << (ostream& os, const Theorem& t) { os << show(t); return os; }
inline ostream& operator << (ostream& os, const Proof& p) { os << show(p); return os; }
inline ostream& operator << (ostream& os, const Step& s)  { os << show(s); return os; }
inline ostream& operator << (ostream& os, const Ref& r)   { os << show(r); return os; }
inline ostream& operator << (ostream& os, const Qed& q)   { os << show(q); return os; }
inline ostream& operator << (ostream& os, const Claim& c) { os << show(c); return os; }
inline ostream& operator << (ostream& os, const Hyp& h)   { os << show(h); return os; }
inline ostream& operator << (ostream& os, const Prop& p)  { os << show(p); return os; }
inline ostream& operator << (ostream& os, const Node& n)  { os << show(n); return os; }
inline ostream& operator << (ostream& os, const Import& i){ os << show(i); return os; }
inline ostream& operator << (ostream& os, const Theory& t){ os << show(t); return os; }
inline ostream& operator << (ostream& os, const Source& s){ os << show(s); return os; }

}} // mdl::rus

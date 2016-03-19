#pragma once

#include <boost/variant/recursive_variant.hpp>
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

void parse(Expr& ex, const vector<Vars>& varsStack, bool prim);

struct Disj {
	vector<vector<Symbol>> d;
};

struct Rule;

struct Type {
	uint id;
	vector<Type*> sup;
	vector<Type*> inf;
	Tree<Rule*>   rules;
};

struct Rule {
	~Rule() { term.destroy(); }
	uint  id;
	Type* type;
	Vars  vars;
	Expr  term;
};

struct Hyp {
	~Hyp() { expr.destroy(); }
	uint ind;
	Expr expr;
};

struct Prop {
	~Prop() { expr.destroy(); }
	uint ind;
	Expr expr;
};

struct Proof;

struct Assertion {
	~ Assertion() {
		for (auto h : hyps) delete h;
		for (auto p : props) delete p;
	}
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
	Assertion ass;
	Assertion def;
};

struct Proof;

struct Theorem {
	Assertion      ass;
	vector<Proof*> proofs;
};

struct Step;

struct Ref {
	enum Kind {
		NONE,
		HYP,
		PROP,
		STEP
	};
	union Value {
		void*  non;
		Hyp*   hyp;
		Prop*  prop;
		Step*  step;
	};
	Ref() : kind(NONE), val() { val.non = nullptr; }
	Ref(Hyp* h)   : kind(HYP),  val()  { val.hyp = h; }
	Ref(Prop* p)  : kind(PROP), val()  { val.prop = p; }
	Ref(Step* s)  : kind(STEP), val()  { val.step = s; }

	Kind kind;
	Value val;
};


struct Step {
	enum Kind {
		NONE,
		AXM,
		THM,
		DEF,
		CLAIM
	};
	union Ass {
		void*    non;
		Axiom*   axm;
		Def*     def;
		Theorem* thm;
		Proof*   prf;
	};

	Step() : ind(-1), expr(), kind(NONE), ass(), refs(), sub() { ass.non = nullptr; }
	~Step() { expr.destroy(); }
	uint        ind;
	Expr        expr;
	Kind        kind;
	Ass         ass;
	vector<Ref> refs;
	Sub<>       sub;
};

struct Qed {
	Prop* prop;
	Step* step;
};

struct Proof {
	//typedef boost::variant<Step, Qed> Elem;

	struct Elem {
		enum Kind {
			NONE,
			VARS,
			STEP,
			QED
		};
		union Value {
			void* non;
			Vars* vars;
			Step* step;
			Qed*  qed;
		};
		Elem() : kind(NONE), val() { val.non = nullptr; }
		Elem(Vars* v)  : kind(VARS), val()  { val.vars = v; }
		Elem(Step* s)  : kind(STEP), val()  { val.step = s; }
		Elem(Qed* q)   : kind(QED), val()   { val.qed = q; }
		void destroy();

		Kind kind;
		Value val;
	};

	Proof() : id(-1), vars(), elems(), thm(nullptr), par(nullptr) { }
	~ Proof() { for (auto& e : elems) e.destroy(); }

	uint         id;
	Vars         vars;
	vector<Elem> elems;
	Theorem*     thm;
	Proof*       par;
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
	~ Theory() { for (auto& n : nodes) n.destroy(); }

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


inline void Proof::Elem::destroy() {
	switch (kind) {
	case STEP : delete val.step; break;
	case VARS:  delete val.vars; break;
	case QED:   delete val.qed; break;
	default : assert(false && "impossible"); break;
	}
	kind = NONE;
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
inline ostream& operator << (ostream& os, const Hyp& h)   { os << show(h); return os; }
inline ostream& operator << (ostream& os, const Prop& p)  { os << show(p); return os; }
inline ostream& operator << (ostream& os, const Node& n)  { os << show(n); return os; }
inline ostream& operator << (ostream& os, const Import& i){ os << show(i); return os; }
inline ostream& operator << (ostream& os, const Theory& t){ os << show(t); return os; }
inline ostream& operator << (ostream& os, const Source& s){ os << show(s); return os; }

}} // mdl::rus

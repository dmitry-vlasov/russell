#pragma once

#include "sys.hpp"
#include "expr.hpp"

namespace mdl { namespace rus {

struct Rule;
struct Proof;
struct Step;
struct Theory;
struct Import;
struct Source;

struct Comment {
	string text;
	Token  token;
};

struct Const : public Owner<Const> {
	Const(Symbol s, Symbol a, Symbol l);
	Symbol symb;
	Symbol ascii;
	Symbol latex;
	Token  token;
};

struct Vars {
	vector<Symbol> v;
	Token token;
};

struct Disj {
	vector<vector<Symbol>> d;
	Token token;
};

void parse_expr(Expr& ex);
void parse_term(Expr& ex, Rule* rule);

struct Type : public Owner<Type> {
	typedef map<const Type*, Rule*> Supers;
	Type(uint id);
	Type(uint id, const vector<Type*>& sup);
	~Type() override;
	vector<User<Type>> sup;
	Supers supers;
	Rules rules;
	Token token;
};

struct Rule : public Owner<Rule> {
	Rule(uint id, uint tp);
	Rule(uint id, uint tp, const Vars& v);
	User<Type> type;
	Vars       vars;
	Expr       term;
	Token      token;
};

inline Type* Tree::type() { return kind == VAR ? val.var->type.get() : val.node->rule.get()->type.get(); }
inline const Type* Tree::type() const { return kind == VAR ? val.var->type.get() : val.node->rule.get()->type.get(); }

struct Hyp {
	uint  ind;
	Expr  expr;
	Token token;
};

struct Prop {
	uint  ind;
	Expr  expr;
	Token token;
};

struct Assertion : public Owner<Assertion> {
	enum Kind {
		AXM,
		THM,
		DEF
	};
	Assertion(uint id);
	~ Assertion() override;
	uint arity() const { return hyps.size(); }
	virtual Kind kind() const = 0;

	Vars vars;
	Disj disj;
	vector<Hyp*>  hyps;
	vector<Prop*> props;
	Token         token;
	Assertion&    ass = *this;
};

struct Axiom : public Assertion {
	Axiom(uint id);
	Kind kind() const { return AXM; }
};

struct Def : public Assertion {
	Def(uint id);
	Kind kind() const { return DEF; }
	Expr dfm;
	Expr dfs;
	Expr prop;
};

struct Theorem : public Assertion {
	Theorem(uint id);
	Kind kind() const { return THM; }
	vector<Proof*> proofs;
};

struct Ref {
	enum Kind {
		NONE,
		HYP,
		PROP,
		STEP
	};
	union Value {
		Value() : non(nullptr) { }
		Value(Hyp* h) : hyp(h) { }
		Value(Prop* p) : prop(p) { }
		Value(Step* s) : step(s) { }
		void*  non;
		Hyp*   hyp;
		Prop*  prop;
		Step*  step;
	};
	Ref() : kind(NONE), val() { }
	Ref(Hyp* h)   : kind(HYP),  val(h)  { }
	Ref(Prop* p)  : kind(PROP), val(p)  { }
	Ref(Step* s)  : kind(STEP), val(s)  { }
	Expr& expr();
	const Expr& expr() const;

	Kind kind;
	Value val;
};

struct Step {
	enum Kind {
		NONE,
		ASS,
		CLAIM
	};
	union Value {
		void*            non;
		User<Assertion>* ass;
		Proof*           prf;
	};

	Step(uint ind, Step::Kind, Assertion::Kind, uint id, Proof* proof);
	~Step();

	Assertion* ass() {
		if (kind_ != ASS) return nullptr;
		return val_.ass->get();
	}
	const Assertion* ass() const {
		if (kind_ != ASS) return nullptr;
		return val_.ass->get();
	}
	Proof* proof() {
		if (kind_ != CLAIM) return nullptr;
		return val_.prf;
	}
	const Proof* proof() const {
		if (kind_ != CLAIM) return nullptr;
		return val_.prf;
	}
	Kind kind() const { return kind_; }
	uint ind() const { return ind_; }
	void set_ind(uint ind) { ind_ = ind; }

	Expr        expr;
	vector<Ref> refs;
	Token       token;

private:
	uint   ind_;
	Kind   kind_;
	Value  val_;
	Proof* proof_;
};

inline Expr& Ref::expr() {
	switch (kind) {
	case HYP : return val.hyp->expr;
	case PROP: return val.prop->expr;
	case STEP: return val.step->expr;
	default  : assert(false && "impossible");
	}
	return val.step->expr;
}

inline const Expr& Ref::expr() const {
	switch (kind) {
	case HYP : return val.hyp->expr;
	case PROP: return val.prop->expr;
	case STEP: return val.step->expr;
	default  : assert(false && "impossible");
	}
	return val.step->expr;
}

struct Qed {
	Prop* prop;
	Step* step;
	Token token;
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

	Proof(Theorem* thm, uint id = -1);
	~ Proof();

	uint         id;
	Vars         vars;
	vector<Elem> elems;
	Theorem*     thm;
	Proof*       par;
	bool         has_id;
	Token        token;
};

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
		IMPORT,
		COMMENT
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
		Comment* com;
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
	Node(Comment* c) : kind(COMMENT), val() { val.com = c; }
	void destroy();

	bool operator==(const Node& n) { return val.non == n.val.non; }

	Kind kind;
	Value val;
};

struct Import {
	Import(Source* src, bool prim) : source(src), primary(prim) { }
	Source* source;
	bool    primary;
	Token   token;
};

struct Theory {
	Theory() : id(-1), nodes(), parent(nullptr) { }
	Theory(uint n, Theory* p) : id(n), nodes(), parent(p) { }
	~ Theory() { for (auto& n : nodes) n.destroy(); }

	uint         id;
	vector<Node> nodes;
	Theory*      parent;
	Token        token;
};

struct Source : public mdl::Source<Source, Sys> {
	Source(uint l);
	~Source();

	Theory* theory;
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
	case COMMENT: delete val.com; break;
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
string show(const Assertion&);
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
string show(const Comment&);

inline ostream& operator << (ostream& os, const Const& c)   { os << show(c); return os; }
inline ostream& operator << (ostream& os, const Vars& v)    { os << show(v); return os; }
inline ostream& operator << (ostream& os, const Disj& d)    { os << show(d); return os; }
inline ostream& operator << (ostream& os, const Type& t)    { os << show(t); return os; }
inline ostream& operator << (ostream& os, const Rule& r)    { os << show(r); return os; }
inline ostream& operator << (ostream& os, const Axiom& a)   { os << show(a); return os; }
inline ostream& operator << (ostream& os, const Def& d)     { os << show(d); return os; }
inline ostream& operator << (ostream& os, const Theorem& t) { os << show(t); return os; }
inline ostream& operator << (ostream& os, const Proof& p)   { os << show(p); return os; }
inline ostream& operator << (ostream& os, const Step& s)    { os << show(s); return os; }
inline ostream& operator << (ostream& os, const Ref& r)     { os << show(r); return os; }
inline ostream& operator << (ostream& os, const Qed& q)     { os << show(q); return os; }
inline ostream& operator << (ostream& os, const Hyp& h)     { os << show(h); return os; }
inline ostream& operator << (ostream& os, const Prop& p)    { os << show(p); return os; }
inline ostream& operator << (ostream& os, const Node& n)    { os << show(n); return os; }
inline ostream& operator << (ostream& os, const Import& i)  { os << show(i); return os; }
inline ostream& operator << (ostream& os, const Theory& t)  { os << show(t); return os; }
inline ostream& operator << (ostream& os, const Source& s)  { os << show(s); return os; }
inline ostream& operator << (ostream& os, const Comment& c) { os << show(c); return os; }

void dump(const Const& c);
void dump(const Vars& v);
void dump(const Disj& d);
void dump(const Type& t);
void dump(const Rule& r);
void dump(const Axiom& a);
void dump(const Def& d);
void dump(const Assertion& a);
void dump(const Theorem& t);
void dump(const Proof& p);
void dump(const Step& s);
void dump(const Ref& r);
void dump(const Qed& q);
void dump(const Hyp& h);
void dump(const Prop& p);
void dump(const Node& n);
void dump(const Import& i);
void dump(const Theory& t);
void dump(const Source& s);
void dump(const Comment& c);

size_t memvol(const Const&);
size_t memvol(const Vars&);
size_t memvol(const Disj&);
size_t memvol(const Type&);
size_t memvol(const Rule&);
size_t memvol(const Axiom&);
size_t memvol(const Def&);
size_t memvol(const Assertion&);
size_t memvol(const Theorem&);
size_t memvol(const Proof&);
size_t memvol(const Step&);
size_t memvol(const Ref&);
size_t memvol(const Qed&);
size_t memvol(const Hyp&);
size_t memvol(const Prop&);
size_t memvol(const Node&);
size_t memvol(const Import&);
size_t memvol(const Theory&);
size_t memvol(const Source&);
size_t memvol(const Comment&);

}} // mdl::rus

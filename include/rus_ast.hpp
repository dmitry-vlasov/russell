#pragma once

#include "rus_expr.hpp"
#include "rus_sys.hpp"

namespace mdl { namespace rus {

struct Rule;
struct Proof;
struct Step;
struct Theory;
struct Import;
struct Source;

struct Comment : public Tokenable {
	Comment(const string& txt, const Token& t = Token()) : Tokenable(t), text(txt) { }
	string text;
};

struct Const : Owner<Const> {
	Const(uint s, uint a, uint l, const Token& t = Token()) :
		Owner(s, t), symb(s), ascii(a), latex(l) { }
	Const(const Const& c) :
		Owner(c.id(), c.token), symb(c.symb), ascii(c.ascii), latex(c.latex) { }
	uint  symb;
	uint  ascii;
	uint  latex;
};

struct Vars : public Tokenable {
	Vars(const vector<Symbol>& vars = vector<Symbol>(), const Token& t = Token()) : Tokenable(t), v(vars) { }
	Vars(const Vars& vars) : Tokenable(vars), v(vars.v) { }
	vector<Symbol> v;
};

struct Disj : public Tokenable {
	Disj(const vector<vector<Symbol>>& disj = vector<vector<Symbol>>(), const Token& t = Token()) :
		Tokenable(t), d(disj) { }
	Disj(const Disj& disj) : Tokenable(disj), d(disj.d) { }
	vector<vector<Symbol>> d;
};

void parse_expr(Expr& ex);

struct Type : public Owner<Type> {
	typedef map<const Type*, Rule*> Supers;
	Type(Id id, const vector<Id>& sup = vector<Id>(), const Token& t = Token());
	~Type() override;
	vector<User<Type>> sup;
	Supers supers;
	Rules  rules;
};

inline bool operator < (const Type& t1, const Type& t2) {
	for (const auto& t : t1.sup) if (t.get() == &t2) return true;
	return false;
}

struct Rule : public Owner<Rule> {
	Rule(Id id, const Vars& v, const Expr& e, const Token& t = Token());
	Vars vars;
	Expr term;
	Type* type() { return term.type.get(); }
	const Type* type() const { return term.type.get(); }
	uint arity() const { return term.tree.arity(); }
};

Rule* find_super(const Type* type, const Type* super);

inline Type* Tree::type() { return kind == VAR ? val.var->type() : val.node->rule.get()->term.type.get(); }
inline const Type* Tree::type() const { return kind == VAR ? val.var->type() : val.node->rule.get()->term.type.get(); }

struct Hyp : public Tokenable {
	Hyp(uint i, const Expr& e = Expr(), const Token& t = Token()) :
		Tokenable(t), ind(i), expr(e) { }
	uint ind;
	Expr expr;
};

struct Prop : public Tokenable {
	Prop(uint i, const Expr& e = Expr(), const Token& t = Token()) :
		Tokenable(t), ind(i), expr(e) { }
	uint ind;
	Expr expr;
};

struct Assertion : public Owner<Assertion> {
	enum Kind { AXM, THM, DEF };
	Assertion(Id id, const Token& t = Token());
	~ Assertion() override;
	uint arity() const { return hyps.size(); }
	virtual Kind kind() const = 0;
	string kindStr() const {
		switch (kind()) {
		case AXM : return "axiom";
		case THM : return "theorem";
		case DEF : return "definition";
		default  : return "<none>";
		}
	}

	Vars vars;
	Disj disj;
	vector<Hyp*>  hyps;
	vector<Prop*> props;
};

struct Axiom : public Assertion {
	Axiom(Id id, const Token& t = Token());
	Kind kind() const { return AXM; }
};

struct Def : public Assertion {
	Def(Id id, const Token& t = Token());
	Kind kind() const { return DEF; }
	Expr dfm;
	Expr dfs;
	Expr prop;
};

struct Theorem : public Assertion {
	Theorem(Id id, const Token& t = Token());
	Kind kind() const { return THM; }
	vector<User<Proof>> proofs;
};

struct Ref : public Tokenable {
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
	Ref(const Token& t = Token()) : Tokenable(t), kind(NONE), val() { }
	Ref(Hyp* h, const Token& t = Token())  : Tokenable(t), kind(HYP),  val(h)  { }
	Ref(Prop* p, const Token& t = Token()) : Tokenable(t), kind(PROP), val(p)  { }
	Ref(Step* s, const Token& t = Token()) : Tokenable(t), kind(STEP), val(s)  { }
	Expr& expr();
	const Expr& expr() const;

	Kind kind;
	Value val;
};

struct Step : public Tokenable {
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

	Step(uint ind, Step::Kind, Assertion::Kind, Id id, Proof* proof, const Token& t = Token());
	~Step();

	Assertion* ass() {
		if (kind_ != ASS) return nullptr;
		return val_.ass->get();
	}
	const Assertion* ass() const {
		if (kind_ != ASS) return nullptr;
		return val_.ass->get();
	}
	Proof* claim() {
		if (kind_ != CLAIM) return nullptr;
		return val_.prf;
	}
	const Proof* claim() const {
		if (kind_ != CLAIM) return nullptr;
		return val_.prf;
	}
	Proof* proof() { return proof_; }
	const Proof* proof() const { return proof_; }
	Kind kind() const { return kind_; }
	uint ind() const { return ind_; }
	void set_ind(uint ind) { ind_ = ind; }

	Expr         expr;
	vector<Ref*> refs;

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

struct Qed : public Tokenable {
	Qed(Prop* p = nullptr, Step* s = nullptr, const Token& t = Token()) :
		Tokenable(t), prop(p), step(s) { }
	Prop* prop;
	Step* step;
};

struct Proof : public Owner<Proof> {
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

	Proof(Theorem* thm, Id id = Id(), const Token& t = Token());
	~ Proof();

	Vars         vars;
	vector<Elem> elems;
	Theorem*     thm;
	Proof*       par;
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

struct Import : public Tokenable {
	Import(uint src, bool prim, const Token& t = Token()) :
		Tokenable(t), source(src), primary(prim) { }
	User<Source> source;
	bool         primary;
};

struct Theory : public Tokenable {
	Theory(const Token& t = Token()) :
		Tokenable(t), id(-1), nodes(), parent(nullptr) { }
	Theory(uint n, Theory* p, const Token& t = Token()) :
		Tokenable(t), id(n), nodes(), parent(p) { }
	~ Theory() { for (auto& n : nodes) n.destroy(); }

	uint         id;
	vector<Node> nodes;
	Theory*      parent;
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

string xml(const Const&, uint);
//string xml(const Vars&, uint);
//string xml(const Disj&, uint);
string xml(const Type&, uint);
string xml(const Rule&, uint);
//string xml(const Axiom&, uint);
//string xml(const Def&, uint);
string xml(const Assertion&, uint);
//string xml(const Theorem&, uint);
string xml(const Proof&, uint);
//string xml(const Step&, uint);
//string xml(const Ref&, uint);
//string xml(const Qed&, uint);
//string xml(const Hyp&, uint);
//string xml(const Prop&, uint);
string xml(const Node&, uint);
string xml(const Import&, uint);
string xml(const Theory&, uint);
string xml_outline(const Source&, uint);
//string xml(const Comment&, uint);

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

void add_to_index(Assertion*);
void add_to_index(Proof*);
Proof* prove(Assertion*);

}} // mdl::rus

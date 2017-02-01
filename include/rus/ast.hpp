#pragma once
#include <boost/algorithm/string.hpp>
//#include <boost/variant/recursive_variant.hpp>
#include "common.hpp"
#include "expr.hpp"

namespace mdl { namespace rus {

struct Comment {
	string text;
};

struct Const {
	uint   ind;
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

void parse_expr(Expr& ex);
void parse_term(Expr& ex, Rule* rule);

struct Type {
	~Type();
	uint ind;
	uint id;
	vector<Type*>     sup;
	map<const Type*, Rule*> supers;
	Rules             rules;
};

struct Rule {
	uint  ind;
	uint  id;
	Type* type;
	Vars  vars;
	Expr  term;
};

inline Type* Tree::type() { return kind == VAR ? val.var->type : val.node->rule->type; }
inline const Type* Tree::type() const { return kind == VAR ? val.var->type : val.node->rule->type; }

inline Type::~Type() {
	for (auto p : supers) delete p.second;
}

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
	~ Assertion() {
		for (auto h : hyps) delete h;
		for (auto p : props) delete p;
	}
	uint arity() const { return hyps.size(); }
	uint ind;
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
	Expr dfm;
	Expr dfs;
	Expr prop;
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
	Expr& expr();
	const Expr& expr() const;

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
	union Value {
		void*    non;
		Axiom*   axm;
		Def*     def;
		Theorem* thm;
		Proof*   prf;
	};

	Step(Proof* pr) : ind(-1), expr(), kind(NONE), val(),
	refs(), proof(pr) { val.non = nullptr; }

	Assertion* assertion() {
		switch(kind) {
		case Step::AXM: return &val.axm->ass;
		case Step::THM: return &val.thm->ass;
		case Step::DEF: return &val.def->ass;
		default : assert(false && "impossible");
		}
		return nullptr;
	}
	const Assertion* assertion() const {
		switch(kind) {
		case Step::AXM: return &val.axm->ass;
		case Step::THM: return &val.thm->ass;
		case Step::DEF: return &val.def->ass;
		default : assert(false && "impossible");
		}
		return nullptr;
	}

	uint        ind;
	Expr        expr;
	Kind        kind;
	Value       val;
	vector<Ref> refs;
	Proof*      proof;
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

	Proof() : ind(-1), id(-1), vars(), elems(), thm(nullptr), par(nullptr), has_id(false) { }
	~ Proof() { for (auto& e : elems) e.destroy(); }

	uint         ind;
	uint         id;
	Vars         vars;
	vector<Elem> elems;
	Theorem*     thm;
	Proof*       par;
	bool         has_id;
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

struct Source;

struct Import {
	Import(Source* src, bool prim) : source(src), primary(prim) { }
	~Import();
	Source* source;
	bool    primary;
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
	Source(const string& r, const string& n) :
	top(false), root(r), name(n), data(), theory(nullptr) {
		static bool t = true; top = t; t = false;
		boost::erase_last(name, ".smm");
		boost::erase_last(name, ".mm");
		boost::erase_last(name, ".rus");
	}
	~Source() { if (theory) delete theory; }
	bool    top;
	string  root;
	string  name;
	string  data;
	string  path() { return (root.size() ? root + "/" + name : name) + ".rus"; }
	string  dir() { string p = path(); return p.substr(0, p.find_last_of("/")) + "/"; }
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

inline Import::~Import() {
	if (primary && source) delete source;
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

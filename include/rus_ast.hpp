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

struct Comment : public Tokenable, public Writable  {
	Comment(bool ml = false, const string& txt = string(), const Token& t = Token()) : Tokenable(t), text(txt), multiline(ml) { }
	string text;
	bool multiline;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Const : public Owner<Const>, public Writable {
	Const(uint s, uint a, uint l, const Token& t = Token()) :
		Owner(s, t), symb(s), ascii(a), latex(l) { }
	Const(const Const& c) :
		Owner(c.id(), c.token), symb(c.symb), ascii(c.ascii), latex(c.latex) { }
	uint  symb;
	uint  ascii;
	uint  latex;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Vars : public Tokenable, public Writable {
	Vars(const vector<Symbol>& vars = vector<Symbol>(), const Token& t = Token()) : Tokenable(t), v(vars) { }
	Vars(const Vars& vars) : Tokenable(vars), v(vars.v) { }
	vector<Symbol> v;
	bool isDeclared(Symbol w) const {
		return std::find(v.begin(), v.end(), w) != v.end();
	}
	void write(ostream& os, const Indent& = Indent()) const override;
};

struct Disj : public Tokenable, public Writable {
	Disj(const vector<vector<Symbol>>& disj = vector<vector<Symbol>>(), const Token& t = Token()) :
		Tokenable(t), d(disj) { }
	Disj(const Disj& disj) : Tokenable(disj), d(disj.d) { }
	vector<vector<Symbol>> d;
	void write(ostream& os, const Indent& = Indent()) const override;
};

void parse_expr(Expr& ex);

struct Type : public Owner<Type>, public Writable {
	typedef map<const Type*, Rule*> Supers;
	Type(Id id, const vector<Id>& sup = vector<Id>(), const Token& t = Token());
	~Type() override;
	vector<User<Type>> sup;
	Supers supers;
	Rules  rules;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

inline bool operator < (const Type& t1, const Type& t2) {
	for (const auto& t : t1.sup) if (t.get() == &t2) return true;
	return false;
}

struct Rule : public Owner<Rule>, public Writable {
	Rule(Id id, const Vars& v, const Expr& e, const Token& t = Token());
	Vars vars;
	Expr term;
	Type* type() { return term.type.get(); }
	const Type* type() const { return term.type.get(); }
	uint arity() const { return term.tree.arity(); }
	void write(ostream& os, const Indent& i = Indent()) const override;
};

Rule* find_super(const Type* type, const Type* super);

inline Type* Tree::type() { return kind == VAR ? val.var->type() : val.node->rule.get()->term.type.get(); }
inline const Type* Tree::type() const { return kind == VAR ? val.var->type() : val.node->rule.get()->term.type.get(); }

struct Hyp : public Tokenable, public Writable {
	Hyp(uint i, const Expr& e = Expr(), const Token& t = Token()) :
		Tokenable(t), ind(i), expr(e) { }
	uint ind;
	Expr expr;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Prop : public Tokenable, public Writable {
	Prop(uint i, const Expr& e = Expr(), const Token& t = Token()) :
		Tokenable(t), ind(i), expr(e) { }
	uint ind;
	Expr expr;
	void write(ostream& os, const Indent& i = Indent()) const override;
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
	void write(ostream& os, const Indent& i = Indent()) const;
};

struct Axiom : public Assertion, public Writable {
	Axiom(Id id, const Token& t = Token());
	Kind kind() const { return AXM; }
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Def : public Assertion, public Writable {
	Def(Id id, const Token& t = Token());
	Kind kind() const { return DEF; }
	Expr dfm;
	Expr dfs;
	Expr prop;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Theorem : public Assertion, public Writable {
	Theorem(Id id, const Token& t = Token());
	Kind kind() const { return THM; }
	vector<User<Proof>> proofs;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Ref : public Tokenable, public Writable {
	enum Kind { HYP, PROP, STEP };
	Kind kind() const { return static_cast<Kind>(val.index()); }
	Ref(Hyp* h, const Token& t = Token())  : Tokenable(t), val(h)  { }
	Ref(Prop* p, const Token& t = Token()) : Tokenable(t), val(p)  { }
	Ref(Step* s, const Token& t = Token()) : Tokenable(t), val(s)  { }
	Expr& expr();
	const Expr& expr() const;
	Hyp* hyp() const { return std::get<Hyp*>(val); }
	Prop* prop() const { return std::get<Prop*>(val); }
	Step* step() const { return std::get<Step*>(val); }

	typedef variant<Hyp*, Prop*, Step*> Value;
	Value val;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Verifiable {
	virtual ~Verifiable() { }
	virtual void verify() const = 0;
	bool check() const {
		try {
			verify();
			return true;
		} catch (Error&) {
			return false;
		}
	}
};

struct Step : public Tokenable, public Verifiable, public Writable {
	enum Kind { ASS, CLAIM };
	typedef variant<User<Assertion>, unique_ptr<Proof>> Value;

	Step(uint i, Step::Kind k, Id id, Proof* p, const Token& t = Token()) :
		Tokenable(t), ind_(i), proof_(p) {
		if (k == ASS) {
			val_ = std::move(User<Assertion>(id));
		}
	}

	Assertion* ass() {
		return (kind() == ASS) ? std::get<User<Assertion>>(val_).get() : nullptr;
	}
	const Assertion* ass() const {
		return (kind() == ASS) ? std::get<User<Assertion>>(val_).get() : nullptr;
	}
	uint ass_id() const {
		return (kind() == ASS) ? std::get<User<Assertion>>(val_).id() : -1;
	}
	Proof* claim() {
		return (kind() == CLAIM) ? std::get<unique_ptr<Proof>>(val_).get() : nullptr;
	}
	const Proof* claim() const {
		return (kind() == CLAIM) ? std::get<unique_ptr<Proof>>(val_).get() : nullptr;
	}
	Proof* proof() { return proof_; }
	const Proof* proof() const { return proof_; }
	Kind kind() const { return static_cast<Kind>(val_.index()); }
	uint ind() const { return ind_; }
	void set_ind(uint ind) { ind_ = ind; }
	void verify() const override;
	void write(ostream& os, const Indent& i = Indent()) const override;

	Expr         expr;
	vector<unique_ptr<Ref>> refs;

private:
	uint   ind_;
	Value  val_;
	Proof* proof_;
};

inline Expr& Ref::expr() {
	switch (kind()) {
	case HYP : return hyp()->expr;
	case PROP: return prop()->expr;
	case STEP: return step()->expr;
	default  : assert(false && "impossible");
	}
	return step()->expr;
}

inline const Expr& Ref::expr() const {
	switch (kind()) {
	case HYP : return hyp()->expr;
	case PROP: return prop()->expr;
	case STEP: return step()->expr;
	default  : assert(false && "impossible");
	}
	return step()->expr;
}

struct Qed : public Tokenable, public Verifiable, public Writable {
	Qed(Prop* p = nullptr, Step* s = nullptr, const Token& t = Token()) :
		Tokenable(t), prop(p), step(s) { }
	void verify() const override;
	Prop* prop;
	Step* step;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Proof : public Owner<Proof>, public Verifiable, public Writable {

	enum Kind { VARS, STEP, QED };
	typedef variant<unique_ptr<Vars>, unique_ptr<Step>, unique_ptr<Qed>> Elem;

	static Kind  kind(const Elem& e) { return static_cast<Kind>(e.index()); }
	static Vars* vars(const Elem& e) { return std::get<unique_ptr<Vars>>(e).get(); }
	static Step* step(const Elem& e) { return std::get<unique_ptr<Step>>(e).get(); }
	static Qed*  qed(const Elem& e) { return std::get<unique_ptr<Qed>>(e).get(); }

	Proof(Id thm, Id id = Id(), const Token& t = Token());

	Theorem* theorem() { return dynamic_cast<Theorem*>(thm.get()); }
	const Theorem* theorem() const { return dynamic_cast<const Theorem*>(thm.get()); }
	void verify() const override;
	vector<Qed*> qeds() const;
	void write(ostream& os, const Indent& i = Indent()) const override;

	Vars            allvars;
	vector<Elem>    elems;
	User<Assertion> thm;
	Proof*          par;
	bool            inner;

};

struct Node : public Writable {
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
	void write(ostream& os, const Indent& i = Indent()) const override;

	Kind kind;
	Value val;
};

struct Import : public Tokenable, public Writable {
	Import(uint src, bool prim, const Token& t = Token()) :
		Tokenable(t), source(src), primary(prim) { }
	User<Source> source;
	bool         primary;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Theory : public Tokenable, public Verifiable, public Writable {
	Theory(const Token& t = Token()) :
		Tokenable(t), id(-1), nodes(), parent(nullptr) { }
	Theory(uint n, Theory* p, const Token& t = Token()) :
		Tokenable(t), id(n), nodes(), parent(p) { }
	~ Theory() { for (auto& n : nodes) n.destroy(); }
	void verify() const override;
	void write(ostream& os, const Indent& i = Indent()) const override;

	uint         id;
	vector<Node> nodes;
	Theory*      parent;
};

struct Source : public mdl::Source<Source, Sys> {
	Source(uint l);
	~Source();
	Tokenable* find(const Token& t);

	Theory* theory;
	void write(ostream& os, const Indent& i = Indent()) const override;
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
bool test_with_oracle();

}} // mdl::rus
